-- Prove2me | solution 1 for BookProof.ChapterContinuityUnitary.condProb_of_continuity
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T21:07:07.827333+00:00
-- url     : https://prove2.me/submissions/5745927b-5407-4621-92f9-d23d01f0977b

import Mathlib
import Definitions.Def_ChapterContinuityUnitary
open BookProof.ChapterContinuityUnitary

variable {N : ℕ} [NeZero N]
variable {X : Type*}

open scoped BigOperators Matrix TensorProduct

theorem solution (v : X → (ZMod N → ℝ)) (t : ℝ)
    (psi : X → ZMod N → ℂ) (hpsi : ∀ x, ∑ z, ‖psi x z‖ ^ 2 = 1) (x : X) :
    (∑' z, bornPMF (v x) t (psi x) (hpsi x) z) = 1 ∧
      ∀ B : Finset (ZMod N),
        ∑ z ∈ B, bornPMF (v x) t (psi x) (hpsi x) z
          = ENNReal.ofReal (bornRecover (v x) t (psi x) B) := by
  constructor
  · simpa using (bornPMF (v x) t (psi x) (hpsi x)).tsum_coe
  · intro B
    simp only [bornPMF, PMF.ofFintype_apply, bornRecover]
    exact (ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)).symm
