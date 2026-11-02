-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_actual_bv_C1_polynomial_error_expectation_first_moment_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T16:23:24.991758+00:00
-- url     : https://prove2.me/submissions/9d527fda-a48b-427e-b0d3-e200caa3ae29

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_integrable_upto_one
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_tail_integrable_upto_one
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_C1_moving_base_residual_polynomial_first_moment_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_C1_random_residual_poly_error_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_random_integrated_error_first_moment_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

/-! Full first-moment Bochner control of the genuine original BV process's
moving-base C1 payoff error against one fixed exponential polynomial. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (hwC1 : ContDiff ℝ 1 w)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|)
    (x M ε : ℝ) (hM : 0 ≤ M) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ p : Polynomial ℝ,
      Polynomial.eval 0 p = 0 ∧
      ∀ t : ℝ≥0, t ≤ 1 →
        |(x + (t : ℝ) * X.drift) - x| < δ →
        |∫ ω, (w (x + (t : ℝ) * X.drift) -
          w (x + X.X t ω)) -
          (∫ r in (0 : ℝ)..((t : ℝ) * X.drift - X.X t ω),
            Polynomial.eval (Real.exp (-r)) p) ∂P| ≤
          ε * (∫ ω, (t : ℝ) * X.drift - X.X t ω ∂P) +
            (2 * L + ε) * (∫ ω,
              if M < (t : ℝ) * X.drift - X.X t ω
              then (t : ℝ) * X.drift - X.X t ω else 0 ∂P) := by
  obtain ⟨δ, hδ, p, hp0, hPoint⟩ :=
    avram_wave5_04c_C1_moving_base_residual_polynomial_first_moment_bound
      w hwC1 L hL hLip x M ε hM hε
  refine ⟨δ, hδ, p, hp0, ?_⟩
  intro t ht hshift
  letI : IsProbabilityMeasure P := X.isProbability
  let R : Ω → ℝ := fun ω => (t : ℝ) * X.drift - X.X t ω
  let b : ℝ := x + (t : ℝ) * X.drift
  have hMeas : Measurable R :=
    measurable_const.sub ((X.adapted t).mono (𝓕.le _) le_rfl)
  have hNonneg : ∀ᵐ ω ∂P, 0 ≤ R ω := by
    filter_upwards [bv_actual_levy_residual_ae_monotone_all_times X hBV]
      with ω hm
    have h0 := hm (show (0 : ℝ≥0) ≤ t from bot_le)
    simpa [R, X.X_zero] using h0
  have hIntR : Integrable R P :=
    avram_wave5_04c_actual_bv_residual_integrable_upto_one X hX hBV t ht
  have hIntTail : Integrable (fun ω => if M < R ω then R ω else 0) P :=
    avram_wave5_04c_actual_bv_residual_tail_integrable_upto_one X hX hBV t ht M
  have hIntE : Integrable (fun ω => (w b - w (b - R ω)) -
      (∫ r in (0 : ℝ)..R ω, Polynomial.eval (Real.exp (-r)) p)) P :=
    avram_wave5_04c_C1_random_residual_poly_error_integrable
      R hMeas hNonneg hIntR w hwC1 L hL hLip p hp0 b
  have hBound : ∀ᵐ ω ∂P,
      |(w b - w (b - R ω)) -
        (∫ r in (0 : ℝ)..R ω, Polynomial.eval (Real.exp (-r)) p)| ≤
      ε * R ω + (2 * L + ε) * (if M < R ω then R ω else 0) := by
    filter_upwards [hNonneg] with ω hω
    exact hPoint b (R ω) hshift hω
  have hh := avram_wave5_04c_random_integrated_error_first_moment_bound
    P R (fun ω => (w b - w (b - R ω)) -
      (∫ r in (0 : ℝ)..R ω, Polynomial.eval (Real.exp (-r)) p))
    M ε L hIntE hIntR hIntTail hBound
  have hcombine (ω : Ω) :
      (x + (t : ℝ) * X.drift) -
        ((t : ℝ) * X.drift - X.X t ω) = x + X.X t ω := by ring
  simpa only [b, R, hcombine] using hh
