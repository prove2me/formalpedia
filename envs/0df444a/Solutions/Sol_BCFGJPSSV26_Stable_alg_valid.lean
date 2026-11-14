-- Prove2me | solution 1 for BCFGJPSSV26.Stable.alg_valid
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T17:57:01.407253+00:00
-- url     : https://prove2.me/submissions/4fdc682f-630f-4db2-888c-ab767b04e38b

module

public import Definitions.Def_BCFGJPSSV26_Stable_Alg_Trial
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_LocalSearch
public import Definitions.Def_BCFGJPSSV26_Stable_Time_Budget
public import Definitions.Def_BCFGJPSSV26_Combine_Analysis
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_Main
import all Definitions.Def_BCFGJPSSV26_Stable_Alg_Main

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset Sampling

variable {I : Instance}

theorem alg_valid (P : Prm) (hv : I.Valid) (hk : I.k ≤ I.m) (L : ℕ) (r : List Bool) :
    I.IsCenterList (alg P ((I, L), r)) ∧ (alg P ((I, L), r)).length = I.k :=
  coreAlg_valid hv hk _ _ _ _

end BCFGJPSSV26.Stable

end

public section

theorem solution : type_of% @BCFGJPSSV26.Stable.alg_valid := @BCFGJPSSV26.Stable.alg_valid
