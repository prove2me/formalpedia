-- Prove2me | solution 1 for BookProof.ChapterDeterministic.commute_projSet_measOpSet_iff_isDeterministic
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T05:42:27.432355+00:00
-- url     : https://prove2.me/submissions/b8937c99-e9bc-44d2-a185-3e6953aeea2c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterDeterministic.lean — solution of BookProof.ChapterDeterministic.commute_projSet_measOpSet_iff_isDeterministic
import Mathlib
import Definitions.Def_ChapterDeterministic
import Theorems.Thm_BookProof_ChapterDeterministic_commute_proj_measOp_iff_isDeterministic
import Theorems.Thm_BookProof_ChapterDeterministic_measOpSet_eq_sum
open BookProof.ChapterDeterministic



open scoped BigOperators
open Finset Matrix
open BookProof.ChapterReconstruct BookProof.ChapterTimeTranslation


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution
    (U : Matrix (Fin n) (Fin n) ℂ) :
    (∀ A B : Finset (Fin n), Commute (projSet A) (measOpSet U B)) ↔ IsDeterministic U := by

  refine ⟨ ?_, fun h => ?_ ⟩;
  · intro hU;
    exact BookProof.ChapterDeterministic.commute_proj_measOp_iff_isDeterministic U |>.1 fun a b =>
        by simpa [ projSet, measOpSet_eq_sum ] using hU { a } { b } ;
  · -- By the single-outcome headline, we have that for all a and b, P_a and U P_b U† commute.
    have h_single : ∀ a b : Fin n, Commute (proj a) (measOp U b) := by
      exact fun a b => ( commute_proj_measOp_iff_isDeterministic U ).mpr h a b;
    exact fun A B => by rw [ measOpSet_eq_sum, projSet ] ;      exact Commute.sum_left _ _ _ fun a _
                        => Commute.sum_right _ _ _ fun b _ => h_single a b;
