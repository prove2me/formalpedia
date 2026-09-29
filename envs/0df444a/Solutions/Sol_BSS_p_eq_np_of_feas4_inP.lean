-- Prove2me | solution 1 for BSS.p_eq_np_of_feas4_inP
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-14T22:13:24.151186+00:00
-- url     : https://prove2.me/submissions/dfb97a23-92d4-4d99-9931-f357cf382d5b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BSS_feas4_np_hard
import Theorems.Thm_BSS_decisionInP_of_polyTimeReduces

open BSS in
/-- The Corollary of §6: if 4-Feasibility is in `P` over `ℝ`, then `P = NP` over `ℝ`.
Every problem in `NP` reduces to 4-Feasibility in polynomial time, and `P` is closed
under polynomial time reductions. -/
theorem solution (hF : DecisionInP Feas4 Feas4Yes) :
    ∀ Z Zyes : Set (Rinf ℝ), Zyes ⊆ Z → DecisionInNP Z Zyes → DecisionInP Z Zyes := by
  intro Z Zyes hsub hNP
  exact BSS.decisionInP_of_polyTimeReduces Z Zyes Feas4 Feas4Yes
    (BSS.feas4_np_hard Z Zyes hsub hNP) hF
