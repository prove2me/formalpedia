-- Prove2me | solution 1 for BookProof.ChapterSolovaySeparableExistence.joint_prob_has_wavefunction
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-30T22:48:52.795775+00:00
-- url     : https://prove2.me/submissions/f3fdd9c2-a1ac-4ec7-b31b-b17790299bf2

-- Generated from ChapterSolovaySeparableExistence.lean — solution of BookProof.ChapterSolovaySeparableExistence.joint_prob_has_wavefunction
import Mathlib
import Definitions.Def_ChapterSolovaySeparableExistence
import Definitions.Def_ChapterSolovayCoordinates
open BookProof.ChapterSolovaySeparableExistence



noncomputable section

open MeasureTheory ProbabilityTheory


open BookProof.ChapterSolovayCoordinates

set_option maxHeartbeats 1000000 in
theorem solution {Z : Type*} [Fintype Z] (p : Z → ℝ)
    (hp : ∀ z, 0 ≤ p z) (hsum : ∑ z, p z = 1) :
    ∃ Ψ : Z → ℂ, (∀ z, ‖Ψ z‖ ^ 2 = p z) ∧ ∑ z, ‖Ψ z‖ ^ 2 = 1 := by

  refine ⟨fun z => (Real.sqrt (p z) : ℂ), fun z => ?_, ?_⟩
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (hp z)]
  · rw [← hsum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (hp z)]
