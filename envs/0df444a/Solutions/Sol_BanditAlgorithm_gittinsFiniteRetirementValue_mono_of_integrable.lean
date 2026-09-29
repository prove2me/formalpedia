-- Prove2me | solution 1 for BanditAlgorithm.gittinsFiniteRetirementValue_mono_of_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-31T04:48:25.853275+00:00
-- url     : https://prove2.me/submissions/79f36a1d-4aef-48b5-b736-1b94108b9bea

import Definitions.Def_GittinsFiniteRetirementValue

open MeasureTheory ProbabilityTheory
open BanditAlgorithm

theorem solution
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) (r : S → ℝ) (α γ : ℝ) (hα0 : 0 ≤ α)
    (hint : ∀ n x, Integrable (gittinsFiniteRetirementValue P r α γ n) (P x)) :
    ∀ n x,
      gittinsFiniteRetirementValue P r α γ n x ≤
        gittinsFiniteRetirementValue P r α γ (n + 1) x := by
  intro n
  induction n with
  | zero =>
      intro x
      simp [gittinsFiniteRetirementValue]
  | succ n ih =>
      intro x
      rw [show gittinsFiniteRetirementValue P r α γ (n + 1) x =
          max 0 (r x - γ +
            α * ∫ y, gittinsFiniteRetirementValue P r α γ n y ∂P x) by rfl]
      rw [show gittinsFiniteRetirementValue P r α γ (n + 1 + 1) x =
          max 0 (r x - γ +
            α * ∫ y, gittinsFiniteRetirementValue P r α γ (n + 1) y ∂P x) by
              congr 2 <;> omega]
      apply max_le_max_left
      have hi := integral_mono (hint n x) (hint (n + 1) x) ih
      have hm := mul_le_mul_of_nonneg_left hi hα0
      linarith
