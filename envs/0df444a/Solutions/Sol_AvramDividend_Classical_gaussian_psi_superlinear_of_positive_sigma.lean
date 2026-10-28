-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_psi_superlinear_of_positive_sigma
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T07:50:54.344045+00:00
-- url     : https://prove2.me/submissions/cc636379-2b01-4f70-b999-2bc65be3a4ec

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_psi_quadratic_lower_from_compensated_negative_jumps
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Gaussian quadratic growth dominates every fixed linear slope. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hσ : 0 < X.σ) :
    ∀ C : ℝ, ∃ β : ℝ, 1 ≤ β ∧
      ∀ θ : ℝ, β ≤ θ → C < X.ψ θ / θ := by
  intro C
  let J : ℝ := ∫ y in Iic (-1 : ℝ), (1 : ℝ) ∂X.ν
  let a : ℝ := X.σ ^ 2 / 2
  have ha : 0 < a := by
    dsimp [a]
    positivity
  let B : ℝ := C - X.c + |J| + 2
  let β : ℝ := max 1 (B / a)
  refine ⟨β, le_max_left _ _, ?_⟩
  intro θ hθ
  have hθone : 1 ≤ θ := le_trans (le_max_left _ _) hθ
  have hθpos : 0 < θ := by linarith
  have hBdiv : B / a ≤ θ :=
    le_trans (le_max_right _ _) hθ
  have hA : B ≤ a * θ := by
    calc
      B ≤ θ * a := (div_le_iff₀ ha).mp hBdiv
      _ = a * θ := mul_comm θ a
  have hAprod : B * θ ≤ (a * θ) * θ :=
    mul_le_mul_of_nonneg_right hA (le_of_lt hθpos)
  have hJabs : J ≤ |J| := le_abs_self J
  have hJnonneg : 0 ≤ |J| := abs_nonneg J
  have hJmul : |J| ≤ |J| * θ := by
    have hm := mul_le_mul_of_nonneg_left hθone hJnonneg
    nlinarith
  have hψ := psi_quadratic_lower_from_compensated_negative_jumps
    X θ (le_of_lt hθpos)
  change X.c * θ + X.σ ^ 2 * θ ^ 2 / 2 - J ≤ X.ψ θ at hψ
  dsimp [B, a] at hAprod
  have hmain : C * θ < X.ψ θ := by
    nlinarith
  exact (lt_div_iff₀ hθpos).2 hmain
