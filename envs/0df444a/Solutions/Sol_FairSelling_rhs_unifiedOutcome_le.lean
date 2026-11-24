-- Prove2me | solution 1 for FairSelling.rhs_unifiedOutcome_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:54:06.045039+00:00
-- url     : https://prove2.me/submissions/749b13d0-313d-4bed-8fea-9e29a3791611

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_TPSSefx
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G]
namespace FairSelling
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ)
    (A : Fin n → Finset G) (F : Finset G) (q : Fin n → ℝ) (i j : Fin n) :
    vbarSum (v i) p ((unifiedOutcome v p A F q).kept j) + (unifiedOutcome v p A F q).money j
      ≤ vbarSum (v i) p (A j) + q j := by
  classical
  have hsplit : vbarSum (v i) p (A j)
      = vbarSum (v i) p ((A j).filter (fun g => ¬ v j g < p g))
        + vbarSum (v i) p ((A j).filter (fun g => v j g < p g)) := by
    unfold vbarSum
    rw [add_comm]
    exact (Finset.sum_filter_add_sum_filter_not (A j) (fun g => v j g < p g) _).symm
  have hle : ∑ g ∈ (A j).filter (fun g => v j g < p g), p g
      ≤ vbarSum (v i) p ((A j).filter (fun g => v j g < p g)) :=
    Finset.sum_le_sum (fun g _ => le_max_left _ _)
  simp only [unifiedOutcome]
  rw [hsplit]
  linarith
end FairSelling
