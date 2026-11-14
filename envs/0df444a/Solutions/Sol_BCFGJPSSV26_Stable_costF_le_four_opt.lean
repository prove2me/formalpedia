-- Prove2me | solution 1 for BCFGJPSSV26.Stable.costF_le_four_opt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:03:44.667409+00:00
-- url     : https://prove2.me/submissions/c8b379e3-29c9-424e-832d-69aa9eaa0534

module

public import Definitions.Def_BCFGJPSSV26_Stable_LocalSearch_Refined
public import Definitions.Def_BCFGJPSSV26_Stable_LocalSearch_ThreeApprox
import all Definitions.Def_BCFGJPSSV26_Stable_LocalSearch_ThreeApprox
public import Theorems.Thm_BCFGJPSSV26_Stable_costF_le_three_add

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

variable {I : Instance}

/-- **Local search is a `4`-approximation.** -/
theorem costF_le_four_opt (hv : I.Valid) (hk : I.k ≤ I.m) {N : ℕ} (hN : 201 ≤ N)
    {S : Finset (Fin I.m)} (hS : IsALO I (24 * N) (1 / (N * I.k)) S) :
    I.costF S ≤ 4 * I.opt I.k := by
  have h := costF_le_three_add hv hk hN hS
  have hopt := Instance.opt_nonneg' hv I.k
  have hN' : (201 : ℝ) ≤ N := by exact_mod_cast hN
  have : (100 : ℝ) / N ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  nlinarith

end BCFGJPSSV26.Stable

end

public section

theorem solution : type_of% @BCFGJPSSV26.Stable.costF_le_four_opt := @BCFGJPSSV26.Stable.costF_le_four_opt
