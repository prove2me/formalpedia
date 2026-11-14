-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a75_original_postpayment_classical_C2_spatial_taylor_finite_mesh_modulus
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:08:07.686608+00:00
-- url     : https://prove2.me/submissions/b0a5ccb8-6b4a-44ef-b59f-351230fc0bf6

import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a58_original_postpayment_finite_mesh_Taylor_modulus_sum
import Theorems.Thm_AvramDividend_Classical_avram_ga_a74_classical_C2_spatial_taylor_polynomial_eq_within_first_order
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Uniform original postpayment compact C2 spatial Taylor quadratic remainder uses the true classical generator derivative, not a within-interval derivative. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbcap : ENNReal.ofReal b < C)
    (hDiff : ∀ z ∈ Icc a b, DifferentiableAt ℝ w z) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (ω : Ω) (S : Finset ℕ) (s : ℕ → ℝ≥0) (y : ℕ → ℝ),
        let z : ℕ → ℝ := fun i =>
          x + X.X (s i) ω - rightLimit D (s i) ω
        (∀ i ∈ S, z i ∈ Icc a b ∧ y i ∈ Icc a b ∧
          z i ≠ y i ∧ dist (y i) (z i) < δ) →
        |∑ i ∈ S, (w (y i) - w (z i) -
          deriv w (z i) * (y i - z i) -
          (iteratedDeriv 2 w (z i) * (y i - z i)^2) / 2)| ≤
          ε * ∑ i ∈ S, (y i - z i)^2 := by
  intro ε hε
  obtain ⟨δ,hδ,hTaylor⟩ :=
    avram_ga_a58_original_postpayment_finite_mesh_Taylor_modulus_sum
      X x D hD C w hw a b ha hab hbcap ε hε
  refine ⟨δ,hδ,?_⟩
  intro ω S s y
  dsimp
  intro hBand
  let z : ℕ → ℝ := fun i =>
    x + X.X (s i) ω - rightLimit D (s i) ω
  have hEq : (∑ i ∈ S, (w (y i) -
      taylorWithinEval w 1 (uIcc (z i) (y i)) (z i) (y i) -
      (iteratedDeriv 2 w (z i) * (y i - z i)^2) / 2)) =
    (∑ i ∈ S, (w (y i) - w (z i) -
      deriv w (z i) * (y i - z i) -
      (iteratedDeriv 2 w (z i) * (y i - z i)^2) / 2)) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hz : DifferentiableAt ℝ w (z i) :=
      hDiff (z i) (hBand i hi).1
    rw [avram_ga_a74_classical_C2_spatial_taylor_polynomial_eq_within_first_order
      w (z i) (y i) (hBand i hi).2.2.1 hz]
    ring
  rw [← hEq]
  exact hTaylor ω S s y hBand
