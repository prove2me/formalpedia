-- Prove2me | solution 1 for ClauseBound.Both.rPow_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:00:01.081284+00:00
-- url     : https://prove2.me/submissions/c80321d1-5e9f-4239-9d21-bb7baa445b0b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FixedWidthVariableBoundStatement
import Definitions.Def_ClauseBound_Both_Defs
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_ClauseBound_Both_TimeM
import Definitions.Def_ClauseBound_Both_End
import Definitions.Def_ClauseBoundStatement
import Definitions.Def_ClauseBound_Inst_Half
import Definitions.Def_ClauseBound_ParityChecks_MasterOL
import Definitions.Def_ClauseBound_ParityChecks_MasterOL
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Gen
import Definitions.Def_ClauseBound_TopN_Gen
import Definitions.Def_ClauseBound_ParityChecks_TopOL
import Definitions.Def_ClauseBound_ParityChecks_CertTopOL
import Definitions.Def_ClauseBound_ParityChecks_CertOL
import Definitions.Def_ClauseBound_ParityChecks_BudgetOL
import Definitions.Def_ClauseBound_ParityChecks_ArithOL
import Definitions.Def_ClauseBound_TopN_Budget
import Definitions.Def_ClauseBound_TopN_Walk
import Definitions.Def_ClauseBound_Gen_End
import Definitions.Def_ClauseBound_Gen_Chain
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Pick
import Definitions.Def_ClauseBound_Gen_Seq
import Definitions.Def_ClauseBound_Inst_HalfEnd
import Definitions.Def_ClauseBound_Inst_CertHalf
import Definitions.Def_ClauseBound_Alg_Enum
import Definitions.Def_ClauseBound_Alg_Grid
import Definitions.Def_ClauseBound_Alg_Level
import Definitions.Def_ClauseBound_Alg_Descend
import Definitions.Def_ClauseBound_Alg_Need
import Definitions.Def_ClauseBound_Alg_NeedC
import Definitions.Def_ClauseBound_Alg_CertEnum
import Definitions.Def_ClauseBound_Alg_CertGridG
import Definitions.Def_ClauseBound_Alg_CertLevel
import Definitions.Def_ClauseBound_Alg_CertTopNet
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_ClauseBound_Alg_TopVal
import Definitions.Def_ClauseBound_Alg_CertTop
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_PaddedDescent_Col_CertG
import Definitions.Def_PaddedDescent_F_CertMark
import Definitions.Def_CountKSatRate_Tree
import Definitions.Def_CountKSatRate_Walk
import Definitions.Def_CountKSatRate_Pad
import Definitions.Def_CountKSatRate_Brute
import Definitions.Def_CountKSatRate_Stack
import Definitions.Def_CountKSat_InOut
import Definitions.Def_ClauseBound_MainBoth
import Theorems.Thm_ClauseBound_Alg_End_one_le_log
import Theorems.Thm_ClauseBound_Gen_End_one_le_log
import Theorems.Thm_ClauseBound_Gen_Rate_one_le_log
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Both
open Groundwork PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.End Levels.Gen ClauseBound.TopN ClauseBound.TopN.Arith ClauseBound.TopN.GenN ClauseBound.ParityChecks
namespace ClauseBound.Both
theorem _root_.solution (α : ℝ) (m : ℕ) : 0 ≤ SatM.rPow α m := by
  unfold SatM.rPow
  exact div_nonneg zero_le_one (Real.rpow_nonneg (by linarith [ClauseBound.Gen.End.one_le_log m]) _)
end ClauseBound.Both
