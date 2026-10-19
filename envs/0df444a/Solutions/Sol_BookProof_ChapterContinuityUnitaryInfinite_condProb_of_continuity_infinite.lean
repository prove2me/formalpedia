-- Prove2me | solution 1 for BookProof.ChapterContinuityUnitaryInfinite.condProb_of_continuity_infinite
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T23:47:01.050305+00:00
-- url     : https://prove2.me/submissions/d6281d94-2793-4adb-a6bc-3832bb7b1443

import Mathlib
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterContinuityUnitary
-- Generated from ChapterContinuityUnitaryInfinite.lean — theorem BookProof.ChapterContinuityUnitaryInfinite.condProb_of_continuity_infinite
open BookProof.ChapterContinuityUnitary
open BookProof.ChapterContinuityUnitaryInfinite


open scoped ENNReal InnerProductSpace

variable {X : Type*}


theorem solution (v : X → LinfZ) (t : ℝ) (psi : X → L2Z)
    (hpsi : ∀ x, ‖psi x‖ = 1) (x : X) :
    (∑' z : ℤ, bornPMF (v x) t (psi x) (hpsi x) z) = 1 ∧
      ∀ B : Finset ℤ,
        ∑ z ∈ B, bornPMF (v x) t (psi x) (hpsi x) z
          = ENNReal.ofReal (bornRecover (v x) t (psi x) B) := by
  refine ⟨PMF.tsum_coe _, fun B => ?_⟩
  rw [BookProof.ChapterContinuityUnitaryInfinite.bornRecover,
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
  rfl

