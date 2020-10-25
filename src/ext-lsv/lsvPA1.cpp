#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <cstdlib>

static int Lsv_CommandPrintUnate(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
    Cmd_CommandAdd(pAbc, "LSV", "lsv_print_sopunate", Lsv_CommandPrintUnate, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
    PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

int cmp(const void *a, const void *b) {
      Abc_Obj_t* obj_a = (Abc_Obj_t*)a;
      Abc_Obj_t* obj_b = (Abc_Obj_t*)b;
      if (Abc_ObjId(obj_a) < Abc_ObjId(obj_b))
          return -1;
      else if (Abc_ObjId(obj_a) == Abc_ObjId(obj_b)) 
          return 0;
      else 
          return 1;
}

void Lsv_NtkPrintUnate(Abc_Ntk_t* pNtk) {
    Abc_Obj_t* pObj;
    Abc_Obj_t* pFanin;
    int i, j, k;
    Abc_NtkForEachNode(pNtk, pObj, i) {
        //printf("Object Id = %d, name = %s\n", Abc_ObjId(pObj), Abc_ObjName(pObj));
        // Get Number of Fim
        //Abc_ObjForEachFanin(pObj, pFanin, j) {
        //printf("  Fanin-%d: Id = %d, name = %s\n", j, Abc_ObjId(pFanin),
        //Abc_ObjName(pFanin));
        //}
        // Need SOP
        if (Abc_NtkHasSop(pNtk)) {
            char* sop = (char*)pObj->pData;
            int num_fanin  = Abc_ObjFaninNum(pObj);
            int num_clause = strlen(sop) / (num_fanin + 3);
            int num_pos_unate = 0;
            int num_neg_unate = 0;
            int num_binate    = 0;
            Abc_Obj_t* pos_unate[num_fanin];
            Abc_Obj_t* neg_unate[num_fanin];
            Abc_Obj_t* binate[num_fanin];

            Abc_ObjForEachFanin(pObj, pFanin, j) {
                int pos_count = 0;
                int neg_count = 0;

                // Counting Literals
                for (k = 0; k < num_clause; ++k) {
                    int idx = k * (num_fanin + 3) + j;
                    if (sop[idx] == '1')
                        pos_count++;
                    else if (sop[idx] == '0')
                        neg_count++;
                    else if (sop[idx] != '-')
                        printf("HAIYAA\n");
                }

                // Check unate/binate
                if (sop[num_fanin + 1] == '1') {
                    // usual case
                    if (pos_count == 0)
                        neg_unate[num_neg_unate++] = pFanin;
                    if (neg_count == 0)
                        pos_unate[num_pos_unate++] = pFanin;
                    if (pos_count != 0 && neg_count != 0)
                        binate[num_binate++] = pFanin;
                }
                else if (sop[num_fanin + 1] == '0') {
                    // unusual case
                    if (neg_count == 0)
                        neg_unate[num_neg_unate++] = pFanin;
                    if (pos_count == 0)
                        pos_unate[num_pos_unate++] = pFanin;
                    if (pos_count != 0 && neg_count != 0)
                        binate[num_binate++] = pFanin;
                }
                else {
                    printf("HAIYAA\n");
                }
            }

            qsort((void*)pos_unate, num_pos_unate, sizeof(Abc_Obj_t*), cmp);
            qsort((void*)neg_unate, num_neg_unate, sizeof(Abc_Obj_t*), cmp);
            qsort((void*)binate   , num_binate   , sizeof(Abc_Obj_t*), cmp);

            printf("node %s:\n", Abc_ObjName(pObj));
            if (num_pos_unate) {
                printf("+unate inputs: %s", Abc_ObjName(pos_unate[0]));
                for (j = 1; j < num_pos_unate; ++j)
                    printf(",%s", Abc_ObjName(pos_unate[j]));
                printf("\n");
            }
            if (num_neg_unate) {
                printf("-unate inputs: %s", Abc_ObjName(neg_unate[0]));
                for (j = 1; j < num_neg_unate; ++j)
                    printf(",%s", Abc_ObjName(neg_unate[j]));
                printf("\n");
            }
            if (num_binate) {
                printf("binate inputs: %s", Abc_ObjName(binate[0]));
                for (j = 1; j < num_binate; ++j)
                    printf(",%s", Abc_ObjName(binate[j]));
                printf("\n");
            }

            //printf(">>%d %d\n", num_fanin, num_clause);
            //printf(">>%d %d %d\n", num_pos_unate, num_neg_unate, num_binate);
            //printf("The SOP of this node:\n%s", (char*)pObj->pData);
        }
    }
}

int Lsv_CommandPrintUnate(Abc_Frame_t* pAbc, int argc, char** argv) {
    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    Extra_UtilGetoptReset();
    while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
        switch (c) {
            case 'h':
                goto usage;
            default:
                goto usage;
        }
    }
    if (!pNtk) {
        Abc_Print(-1, "Empty network.\n");
        return 1;
    }
    Lsv_NtkPrintUnate(pNtk);
    return 0;

usage:
    Abc_Print(-2, "usage: lsv_print_sopunate [-h]\n");
    Abc_Print(-2, "\t        prints the unte information for each node\n");
    Abc_Print(-2, "\t-h    : print the command usage\n");
    return 1;
}
