-- Prove2me | solution 1 for BCFGJPSSV26.Stable.costF_localSearch_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:03:43.637539+00:00
-- url     : https://prove2.me/submissions/1d87b07c-7ae9-43d1-93ee-85467c38db15

module

public import Definitions.Def_BCFGJPSSV26_Stable_Params
public import Definitions.Def_BCFGJPSSV26_Stable_LocalSearch_ThreeApprox
public import Definitions.Def_BuhaiPapers_Background_Tuples
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_LocalSearch
import all Definitions.Def_BCFGJPSSV26_Stable_Alg_LocalSearch
public import Theorems.Thm_BCFGJPSSV26_Stable_costF_le_three_add
public import Theorems.Thm_BCFGJPSSV26_Stable_isALO_localSearch

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Stable

open Tuples Encoding

variable {I : Instance}

/-- **The local search is a `(3 + 100/N)`-approximation** when the budget is large enough. -/
theorem costF_localSearch_le (hv : I.Valid) (hk : I.k ≤ I.m) {N B : ℕ} (hN : 201 ≤ N)
    (hB₁ : (I.k * I.m) ^ Par.p N ≤ B) (hB₂ : 2 * N * I.k * (encInstance I).length + 2 ≤ B) :
    I.costF (I.centers (localSearch N (toRaw I) B)) ≤ (3 + 100 / N) * I.opt I.k :=
  costF_le_three_add hv hk hN (isALO_localSearch hv hk (by omega) hB₁ hB₂)

end BCFGJPSSV26.Stable

end

public section

theorem solution : type_of% @BCFGJPSSV26.Stable.costF_localSearch_le := @BCFGJPSSV26.Stable.costF_localSearch_le
