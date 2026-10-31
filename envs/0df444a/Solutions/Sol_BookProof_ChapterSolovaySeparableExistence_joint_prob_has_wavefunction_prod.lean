-- Prove2me | solution 1 for BookProof.ChapterSolovaySeparableExistence.joint_prob_has_wavefunction_prod
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-30T22:48:56.65238+00:00
-- url     : https://prove2.me/submissions/ff9e6593-57d8-4f9e-96a0-e0e53bf55f40

-- Generated from ChapterSolovaySeparableExistence.lean — solution of BookProof.ChapterSolovaySeparableExistence.joint_prob_has_wavefunction_prod
import Mathlib
import Definitions.Def_ChapterSolovaySeparableExistence
import Theorems.Thm_BookProof_ChapterSolovaySeparableExistence_joint_prob_has_wavefunction
import Definitions.Def_ChapterSolovayCoordinates
open BookProof.ChapterSolovaySeparableExistence



noncomputable section

open MeasureTheory ProbabilityTheory


open BookProof.ChapterSolovayCoordinates

set_option maxHeartbeats 1000000 in
theorem solution {X Y : Type*} [Fintype X] [Fintype Y]
    (p : X × Y → ℝ) (hp : ∀ z, 0 ≤ p z) (hsum : ∑ z, p z = 1) :
    ∃ Ψ : X × Y → ℂ, (∀ z, ‖Ψ z‖ ^ 2 = p z) ∧ ∑ z, ‖Ψ z‖ ^ 2 = 1 ∧
      ∀ x : X, (∑ y : Y, ‖Ψ (x, y)‖ ^ 2) = ∑ y : Y, p (x, y) := by

  obtain ⟨Ψ, hΨ, hΨsum⟩ := joint_prob_has_wavefunction p hp hsum
  exact ⟨Ψ, hΨ, hΨsum, fun x => Finset.sum_congr rfl fun y _ => hΨ (x, y)⟩
