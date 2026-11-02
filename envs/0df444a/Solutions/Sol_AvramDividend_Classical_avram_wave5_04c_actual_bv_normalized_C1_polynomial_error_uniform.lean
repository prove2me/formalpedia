-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_actual_bv_normalized_C1_polynomial_error_uniform
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T17:39:15.833108+00:00
-- url     : https://prove2.me/submissions/9468aba5-6a01-4333-9d02-c66ef1592108

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_C1_polynomial_error_expectation_first_moment_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_normalized_tail_uniform_vanish
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_normalized_mean_le_two_terminal_mean
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

/-! The actual original BV source has an arbitrarily small inverse-time
expected C1 polynomial approximation error, uniform at small positive times. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (hwC1 : ContDiff ℝ 1 w)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|)
    (x ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ p : Polynomial ℝ,
      Polynomial.eval 0 p = 0 ∧
      ∀ h : ℝ≥0, 0 < h → h ≤ (1 / 2 : ℝ≥0) →
        |(x + (h : ℝ) * X.drift) - x| < δ →
        |(h : ℝ)⁻¹ * (∫ ω,
          (w (x + (h : ℝ) * X.drift) - w (x + X.X h ω)) -
            (∫ r in (0 : ℝ)..((h : ℝ) * X.drift - X.X h ω),
              Polynomial.eval (Real.exp (-r)) p) ∂P)| ≤
        ε * (2 * (∫ ω, (1 : ℝ) * X.drift - X.X 1 ω ∂P) +
          2 * L + ε) := by
  have htail :=
    avram_wave5_04c_actual_bv_residual_normalized_tail_uniform_vanish
      X hX hBV ε hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 htail
  have hM : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  obtain ⟨δ, hδ, p, hp0, hbound⟩ :=
    avram_wave5_04c_actual_bv_C1_polynomial_error_expectation_first_moment_bound
      X hX hBV w hwC1 L hL hLip x (N : ℝ) ε hM hε
  refine ⟨δ, hδ, p, hp0, ?_⟩
  intro h hhpos hhhalf hshift
  have hm := avram_wave5_04c_actual_bv_residual_normalized_mean_le_two_terminal_mean
    X hX hBV h hhpos hhhalf
  have ht := hN N le_rfl h hhpos hhhalf
  have hi : 0 ≤ (h : ℝ)⁻¹ :=
    inv_nonneg.mpr (NNReal.coe_nonneg h)
  have hc : 0 ≤ 2 * L + ε := by linarith
  have hb := hbound h (by
    exact le_trans hhhalf (by norm_num)) hshift
  calc
    |(h : ℝ)⁻¹ * (∫ ω,
      (w (x + (h : ℝ) * X.drift) - w (x + X.X h ω)) -
        (∫ r in (0 : ℝ)..((h : ℝ) * X.drift - X.X h ω),
          Polynomial.eval (Real.exp (-r)) p) ∂P)| =
      (h : ℝ)⁻¹ * |∫ ω,
      (w (x + (h : ℝ) * X.drift) - w (x + X.X h ω)) -
        (∫ r in (0 : ℝ)..((h : ℝ) * X.drift - X.X h ω),
          Polynomial.eval (Real.exp (-r)) p) ∂P| := by
            rw [abs_mul, abs_of_nonneg hi]
    _ ≤ (h : ℝ)⁻¹ * (
      ε * (∫ ω, (h : ℝ) * X.drift - X.X h ω ∂P) +
      (2 * L + ε) *
        (∫ ω, if (N : ℝ) < (h : ℝ) * X.drift - X.X h ω
          then (h : ℝ) * X.drift - X.X h ω else 0 ∂P)) :=
            mul_le_mul_of_nonneg_left hb hi
    _ = ε * ((h : ℝ)⁻¹ *
        (∫ ω, (h : ℝ) * X.drift - X.X h ω ∂P)) +
      (2 * L + ε) * ((h : ℝ)⁻¹ *
        (∫ ω, if (N : ℝ) < (h : ℝ) * X.drift - X.X h ω
          then (h : ℝ) * X.drift - X.X h ω else 0 ∂P)) := by ring
    _ ≤ ε * (2 * (∫ ω, (1 : ℝ) * X.drift - X.X 1 ω ∂P)) +
        (2 * L + ε) * ε :=
          add_le_add
            (mul_le_mul_of_nonneg_left hm (le_of_lt hε))
            (mul_le_mul_of_nonneg_left (le_of_lt ht) hc)
    _ = ε * (2 * (∫ ω, (1 : ℝ) * X.drift - X.X 1 ω ∂P) +
        2 * L + ε) := by ring
