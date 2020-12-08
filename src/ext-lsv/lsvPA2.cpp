#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "sat/cnf/cnf.h"
#include <cstdlib>

static int Lsv_CommandPrintPOUnate(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
    Cmd_CommandAdd(pAbc, "LSV", "lsv_print_pounate", Lsv_CommandPrintPOUnate, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
    PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

int cmp(const void *a, const void *b) {
    Abc_Obj_t* obj_a = *(Abc_Obj_t**)a;
    Abc_Obj_t* obj_b = *(Abc_Obj_t**)b;
    //printf("%d %d\n", Abc_ObjId(obj_a), Abc_ObjId(obj_b));
    if (Abc_ObjId(obj_a) < Abc_ObjId(obj_b))
        return -1;
    else if (Abc_ObjId(obj_a) == Abc_ObjId(obj_b)) 
        return 0;
    else 
        return 1;
}

extern "C" Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
extern "C" Abc_Ntk_t * Abc_NtkCreateCone( Abc_Ntk_t * pNtk, Abc_Obj_t * pNode, char * pNodeName, int fUseAllCis );

void Lsv_NtkPrintPOUnate(Abc_Ntk_t* pNtk) {
    Aig_Obj_t* pAigObj;
    Abc_Obj_t* pPO;
    Abc_Obj_t* pPI;
    Abc_Obj_t* pNode;
    Abc_Obj_t* pFanin;
    int i, j, k;

    // Assert AIG
    assert(Abc_NtkIsStrash(pNtk));
    assert(Abc_NtkLatchNum(pNtk) == 0);

    // Convert to AIG
    Aig_Man_t* pMan = Abc_NtkToDar(pNtk, 0, 0);

    // Convert to CNF
    //printf("%d\n", Aig_ManCoNum(pMan));
    Cnf_Dat_t* lCnf = Cnf_Derive(pMan, Aig_ManCoNum(pMan));
    Cnf_Dat_t* rCnf = Cnf_DataDup(lCnf);
    Cnf_DataLift(rCnf, rCnf->nVars);
    
    //Cnf_DataPrint(lCnf, 1);
    //Cnf_DataPrint(rCnf, 1);
    
    // Creat solver
    sat_solver* pSat = (sat_solver *)Cnf_DataWriteIntoSolver(lCnf, 1, 0);
    Cnf_DataWriteIntoSolverInt(pSat, rCnf, 1, 0);
    lit assumptions[4 + Abc_NtkPiNum(pNtk)];

    Abc_NtkForEachPi(pNtk, pPI, i) {
        int aig_id = Abc_ObjId(pPI);
        //printf("%d %d %d %d %d\n", i, Abc_ObjId(pPI), aig_id, lCnf->pVarNums[aig_id], rCnf->pVarNums[aig_id]);
        sat_solver_add_buffer_enable(pSat, lCnf->pVarNums[aig_id], rCnf->pVarNums[aig_id], lCnf->nVars * 2 + i, 0);
        assumptions[4 + i] = Abc_Var2Lit(lCnf->nVars * 2 + i, 0); // Positive
    }

    //printf("        nVars\tnClauses\n");
    //printf("lCNF:   %d\t%d\n", lCnf->nVars, lCnf->nClauses);
    //printf("rCNF:   %d\t%d\n", rCnf->nVars, rCnf->nClauses);
    //printf("SOLVER: %d\t%d\n", sat_solver_nvars(pSat), sat_solver_nclauses(pSat));
    //printf("\n");
    //Abc_Obj_t* rrr;
    //Aig_Obj_t* sss;
    //Abc_NtkForEachObj(pNtk, rrr, i) {
        //printf("Object Id = %d, name = %s\n", Abc_ObjId(rrr), Abc_ObjName(rrr));
    //}
    //printf("%d^^==========vv%d\n", Abc_NtkNodeNum(pNtk), Aig_ManNodeNum(pMan));
    //Aig_ManForEachObj(pMan, sss, i) {
        //printf("Object Id = %d\n", Aig_ObjId(sss));
    //}
    //printf("=====\n");
    //Aig_ManForEachPoSeq(pMan, sss, i) {
        //printf("Object Id = %d\n", Aig_ObjId(sss));
    //}
    //printf("=====\n");
    //Aig_ManForEachPiSeq(pMan, sss, i) {
        //printf("Object Id = %d\n", Aig_ObjId(sss));
    //}
    int is_pu, is_nu;
    int num_punate;
    int num_nunate;
    int num_binate;
    Abc_Obj_t* punate[Abc_NtkPiNum(pNtk)];
    Abc_Obj_t* nunate[Abc_NtkPiNum(pNtk)];
    Abc_Obj_t* binate[Abc_NtkPiNum(pNtk)];

    // For Each PO
    Abc_NtkForEachPo(pNtk, pPO, i) {
        //printf("Object Id = %d, name = %s\n", Abc_ObjId(pPO), Abc_ObjName(pPO));
        int aig_id = Abc_ObjId(pPO) + Abc_NtkNodeNum(pNtk);

        assumptions[0] = Abc_Var2Lit(lCnf->pVarNums[aig_id], 0); // Positive
        assumptions[1] = Abc_Var2Lit(rCnf->pVarNums[aig_id], 1); // Negative
        num_punate = 0;
        num_nunate = 0;
        num_binate = 0;

        Abc_NtkForEachPi(pNtk, pPI, j) {
            assumptions[4 + j] = Abc_Var2Lit(lCnf->nVars * 2 + j, 1); // Negative
            // TEST positive unate
            assumptions[2] = Abc_Var2Lit(lCnf->pVarNums[Abc_ObjId(pPI)], 1);
            assumptions[3] = Abc_Var2Lit(rCnf->pVarNums[Abc_ObjId(pPI)], 0);
            is_pu = sat_solver_solve(pSat, assumptions, assumptions + 4 + Abc_NtkPiNum(pNtk), \
                    (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0);
            // TEST negative unate
            assumptions[2] = Abc_Var2Lit(lCnf->pVarNums[Abc_ObjId(pPI)], 0);
            assumptions[3] = Abc_Var2Lit(rCnf->pVarNums[Abc_ObjId(pPI)], 1);
            is_nu = sat_solver_solve(pSat, assumptions, assumptions + 4 + Abc_NtkPiNum(pNtk), \
                    (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0);
            assumptions[4 + j] = Abc_Var2Lit(lCnf->nVars * 2 + j, 0); // Positive

            if (is_pu == -1)
                punate[num_punate++] = pPI;
            if (is_nu == -1)
                nunate[num_nunate++] = pPI;
            if (is_pu != -1 && is_nu != -1)
                binate[num_binate++] = pPI;
            //printf("%d %d\n", is_pu, is_nu);
        }
        qsort((void*)punate, num_punate, sizeof(Abc_Obj_t*), cmp);
        qsort((void*)nunate, num_nunate, sizeof(Abc_Obj_t*), cmp);
        qsort((void*)binate, num_binate, sizeof(Abc_Obj_t*), cmp);
        printf("node %s:\n", Abc_ObjName(pPO));
        if (num_punate) {
            printf("+unate inputs: %s", Abc_ObjName(punate[0]));
            for (j = 1; j < num_punate; ++j)
                printf(",%s", Abc_ObjName(punate[j]));
            printf("\n");
        }
        if (num_nunate) {
            printf("-unate inputs: %s", Abc_ObjName(nunate[0]));
            for (j = 1; j < num_nunate; ++j)
                printf(",%s", Abc_ObjName(nunate[j]));
            printf("\n");
        }
        if (num_binate) {
            printf("binate inputs: %s", Abc_ObjName(binate[0]));
            for (j = 1; j < num_binate; ++j)
                printf(",%s", Abc_ObjName(binate[j]));
            printf("\n");
        }
        //exit(-1);
        //printf( "CNF stats: Vars = %6d. Clauses = %7d. Literals = %8d. \n",\
                //pCnf->nVars, pCnf->nClauses, pCnf->nLiterals );
    }

    //// For Each PO
    //Abc_NtkForEachPo(pNtk, pPO, i) {
        //printf("\n\n\n");
        ////printf("%p %d\n", pPO, Abc_ObjIsNode(pPO));
        //printf("Object Id = %d, name = %s\n", Abc_ObjId(pPO), Abc_ObjName(pPO));

        //// Get PO Cone
        //pNode = Abc_NtkFindNode(pNtk, Abc_ObjName(pPO));
        //Abc_Ntk_t * pSingPONtk = Abc_NtkCreateCone(pNtk, pNode, Abc_ObjName(pPO), 1);

        //// Convert to AIG
        //Aig_Man_t * pMan = Abc_NtkToDar(pSingPONtk, 0, 0);

        //// Convert to CNF, only one output node after cone
        //Cnf_Dat_t * lCnf = Cnf_Derive(pMan, 1);
        //Cnf_Dat_t * rCnf = Cnf_DataDup(lCnf);
        //Cnf_DataLift(rCnf, rCnf->nVars);
        
        //Cnf_DataPrint(lCnf, 1);
        //Cnf_DataPrint(rCnf, 1);

        //// Creat SAT solver
        //sat_solver * pSat = (sat_solver *)Cnf_DataWriteIntoSolver(lCnf, 1, 0);
        //Cnf_DataWriteIntoSolverInt(pSat, rCnf, 1, 0);

        //lit Ol = Abc_Var2Lit(lCnf->pVarNums[Abc_ObjId(pPO)], 0); // Positive
        //lit Or = Abc_Var2Lit(rCnf->pVarNums[Abc_ObjId(pPO)], 1); // Negative

        //printf("        nVars\tnClauses\n");
        //printf("lCNF:   %d\t%d\n", lCnf->nVars, lCnf->nClauses);
        //printf("rCNF:   %d\t%d\n", rCnf->nVars, rCnf->nClauses);
        //printf("SOLVER: %d\t%d\n", sat_solver_nvars(pSat), sat_solver_nclauses(pSat));

        //exit(-1);
        ////printf( "CNF stats: Vars = %6d. Clauses = %7d. Literals = %8d. \n",\
                ////pCnf->nVars, pCnf->nClauses, pCnf->nLiterals );
        ////Cnf_DataPrint(pCnf, 1);
        ////Aig_ManForEachPiSeq(pMan, pAigObj, j) {
            ////printf(">>%d %d\n", Aig_ObjId(pAigObj), pCnf->pVarNums[Aig_ObjId(pAigObj)]);
        ////}
        ////Aig_ManForEachPoSeq(pMan, pAigObj, j) {
            ////printf("><%d %d\n", Aig_ObjId(pAigObj), pCnf->pVarNums[Aig_ObjId(pAigObj)]);
        ////}
        ////Aig_ManForEachObj(pMan, pAigObj, j) {
            ////printf("<<%d %d\n", Aig_ObjId(pAigObj), pCnf->pVarNums[Aig_ObjId(pAigObj)]);
        ////}

        //// Construct the CNF of Fa->F~a
        //Cnf_Dat_t * pCnf = Cnf_Derive(pMan, 1);
        //int   nVars     = pCnf->nVars;
        //int   nLiterals = pCnf->nLiterals;
        //int   nClauses  = pCnf->nClauses;
        //int** pClauses  = (int**)malloc(sizeof(int*) * (2 * pCnf->nClauses + 10));
        //int*  pLiterals = (int* )malloc(sizeof(int)  * (2 * pCnf->nLiterals + 10));

        //for (int n = 0; n < nClauses; ++n) {
            //int* cla = pLiterals + (pCnf->pClauses[n] - pCnf->pClauses[0]);
            //pClauses[n] = cla;
            //pClauses[n + nClauses] = cla + nLiterals;
        //}
        //pClauses[2 * nClauses    ] = pClauses[0] + nLiterals * 2;
        //pClauses[2 * nClauses + 1] = pClauses[2 * nClauses] + 1;
        //pClauses[2 * nClauses + 2] = pClauses[2 * nClauses] + 2;
        //pClauses[2 * nClauses + 3] = pClauses[2 * nClauses] + 3;
        //pClauses[2 * nClauses + 4] = pClauses[2 * nClauses] + 4;

        //for (int n = 0; n < nLiterals; ++n) {
            //int var = pCnf->pClauses[0][n];
            //pLiterals[n] = var;
            //pLiterals[n + nLiterals] = \
                //Abc_Var2Lit(Abc_Lit2Var(var) + nVars, Abc_LitIsCompl(var));
        //}
        //Aig_ManForEachPoSeq(pMan, pAigObj, j) {
            //*pClauses[2 * nClauses    ] = \
                //Abc_Var2Lit(pCnf->pVarNums[Aig_ObjId(pAigObj)]        , 0);
            //*pClauses[2 * nClauses + 1] = \
                //Abc_Var2Lit(pCnf->pVarNums[Aig_ObjId(pAigObj)] + nVars, 1);
        //}

        //pCnf->nVars     = nVars     * 2;
        //pCnf->nLiterals = nLiterals * 2 + 4;
        //pCnf->nClauses  = nClauses  * 2 + 4;
        //pCnf->pClauses  = pClauses;

        //Aig_ManForEachPiSeq(pMan, pAigObj, j) {
            //// Positive
            //printf(">>%d %d\n", Aig_ObjId(pAigObj), pCnf->pVarNums[Aig_ObjId(pAigObj)]);
            //*pClauses[2 * nClauses + 2] = \
                //Abc_Var2Lit(pCnf->pVarNums[Aig_ObjId(pAigObj)]        , 0);
            //*pClauses[2 * nClauses + 3] = \
                //Abc_Var2Lit(pCnf->pVarNums[Aig_ObjId(pAigObj)] + nVars, 1);
            //Cnf_DataPrint(pCnf, 1);

            //// Convert to SAT
            //sat_solver * pSat = (sat_solver *)Cnf_DataWriteIntoSolver( pCnf, 1, 0 );
            ////printf("%p\n", pSat);
            ////status = sat_solver2_simplify(pSat);
            ////printf( "Simplified the problem to %d variables and %d clauses. ",\
                    ////sat_solver2_nvars(pSat), sat_solver2_nclauses(pSat) );
            ////if ( status == 0 )
            ////{
                ////Vec_IntFree( vCiIds );
                ////sat_solver2_delete( pSat );
                ////printf( "The problem is UNSATISFIABLE after simplification.\n" );
                ////return 1;
            ////}

            //int status = sat_solver_solve( pSat, NULL, NULL, \
                    //(ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
            //if (status == l_Undef) {
                //printf( "The problem timed out.\n" );
            //}
            //else if ( status == l_True ) {
                //printf( "The problem is SATISFIABLE.\n" );
            //}
            //else if ( status == l_False ) {
                //printf( "The problem is UNSATISFIABLE.\n" );
            //}
            //else
                //assert(0);
            //sat_solver_delete( pSat );
        //}


        //pCnf->nVars = pCnf->nVars * 2;

        //int Entry;
        //printf("!!!%p %p\n", s_pManCnf, pCnf->vMapping);
        //Vec_IntForEachEntry(s_pManCnf ->vMapping, Entry, j){
        //printf(">>%d %d\n", j, Entry);
        //}

        // Get Number of Fim
        //Abc_ObjForEachFanin(pObj, pFanin, j) {
        //printf("  Fanin-%d: Id = %d, name = %s\n", j, Abc_ObjId(pFanin),
        //Abc_ObjName(pFanin));
        //}
        // Need SOP
        //if (Abc_NtkHasSop(pNtk)) {
        //char* sop = (char*)pObj->pData;
        //int num_fanin  = Abc_ObjFaninNum(pObj);
        //int num_clause = strlen(sop) / (num_fanin + 3);
        //int num_pos_unate = 0;
        //int num_neg_unate = 0;
        //int num_binate    = 0;
        //Abc_Obj_t* pos_unate[num_fanin];
        //Abc_Obj_t* neg_unate[num_fanin];
        //Abc_Obj_t* binate[num_fanin];

        //// Ignore constant
        //if (!num_fanin)
        //continue;

        //Abc_ObjForEachFanin(pObj, pFanin, j) {
        //int pos_count = 0;
        //int neg_count = 0;

        //// Counting Literals
        //for (k = 0; k < num_clause; ++k) {
        //int idx = k * (num_fanin + 3) + j;
        //if (sop[idx] == '1')
        //pos_count++;
        //else if (sop[idx] == '0')
        //neg_count++;
        //else if (sop[idx] != '-')
        //printf("HAIYAA\n");
        //}

        //// Check unate/binate
        //if (sop[num_fanin + 1] == '1') {
        //// usual case
        //if (pos_count == 0)
        //neg_unate[num_neg_unate++] = pFanin;
        //if (neg_count == 0)
        //pos_unate[num_pos_unate++] = pFanin;
        //if (pos_count != 0 && neg_count != 0)
        //binate[num_binate++] = pFanin;
        //}
        //else if (sop[num_fanin + 1] == '0') {
        //// unusual case
        //if (neg_count == 0)
        //neg_unate[num_neg_unate++] = pFanin;
        //if (pos_count == 0)
        //pos_unate[num_pos_unate++] = pFanin;
        //if (pos_count != 0 && neg_count != 0)
        //binate[num_binate++] = pFanin;
        //}
        //else {
        //printf("HAIYAA\n");
        //}
        //}

        //qsort((void*)pos_unate, num_pos_unate, sizeof(Abc_Obj_t*), cmp);
        //qsort((void*)neg_unate, num_neg_unate, sizeof(Abc_Obj_t*), cmp);
        //qsort((void*)binate   , num_binate   , sizeof(Abc_Obj_t*), cmp);

        //printf("node %s:\n", Abc_ObjName(pObj));
        //if (num_pos_unate) {
        //printf("+unate inputs: %s", Abc_ObjName(pos_unate[0]));
        //for (j = 1; j < num_pos_unate; ++j)
        //printf(",%s", Abc_ObjName(pos_unate[j]));
                //printf("\n");
            //}
            //if (num_neg_unate) {
                //printf("-unate inputs: %s", Abc_ObjName(neg_unate[0]));
                //for (j = 1; j < num_neg_unate; ++j)
                    //printf(",%s", Abc_ObjName(neg_unate[j]));
                //printf("\n");
            //}
            //if (num_binate) {
                //printf("binate inputs: %s", Abc_ObjName(binate[0]));
                //for (j = 1; j < num_binate; ++j)
                    //printf(",%s", Abc_ObjName(binate[j]));
                //printf("\n");
            //}
        //}
    //}
}

int Lsv_CommandPrintPOUnate(Abc_Frame_t* pAbc, int argc, char** argv) {
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
    Lsv_NtkPrintPOUnate(pNtk);
    return 0;

usage:
    Abc_Print(-2, "usage: lsv_print_pounate [-h]\n");
    Abc_Print(-2, "\t        print the unate information for each primary output in terms of all primary inputs, whose function is encoded as an and-inverter graph (AIG).\n");
    Abc_Print(-2, "\t-h    : print the command usage\n");
    return 1;
}
