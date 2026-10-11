-- Prove2me | solution 1 for BookProof.ChapterWeakValue.condProb_eq_weakNumerator_ratio
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:37:41.852489+00:00
-- url     : https://prove2.me/submissions/017ebdd5-3279-452f-9b28-6d565bc64442

-- Generated from ChapterWeakValue.lean — solution of BookProof.ChapterWeakValue.condProb_eq_weakNumerator_ratio
import Mathlib
import Definitions.Def_ChapterWeakValue
import Theorems.Thm_BookProof_ChapterWeakValue_jointProb_eq_normSq_weakNumerator
import Definitions.Def_ChapterTrajectory
open BookProof.ChapterWeakValue



open scoped BigOperators Matrix


variable {n : ℕ}
open BookProof.ChapterTrajectory

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (U V : Matrix (Fin n) (Fin n) ℂ)
    (psi : Fin n → ℂ) (f a : Fin n) :
    condProb U V psi f a =
      ‖ip (postSelect V f) (projMat a *ᵥ (U *ᵥ psi))‖ ^ 2 /
        ∑ b, ‖ip (postSelect V f) (projMat b *ᵥ (U *ᵥ psi))‖ ^ 2 := by

  rw [condProb, finalProb, jointProb_eq_normSq_weakNumerator]
  exact congrArg _
    (Finset.sum_congr rfl fun b _ =>
      (jointProb_eq_normSq_weakNumerator U V psi f b).symm)
