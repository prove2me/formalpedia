-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_actual_BV_original_residual_poly_error_normalized
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:45:07.242822+00:00
-- url     : https://prove2.me/submissions/39fa0eda-43ca-4a19-bd1c-2328ce4d048d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_integrable_upto_one
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_tail_integrable_upto_one
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_random_BV_weighted_polynomial_L1_error
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! The genuine BV source random residual inherits the global C1
weighted polynomial error with exact first-moment/tail expectations. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w)
    (L : ℝ) (hL : 0 ≤ L)
    (x M ε : ℝ) (hε : 0 ≤ ε)
    (Q : Polynomial ℝ)
    (hpoint : ∀ r : ℝ, 0 ≤ r →
      |Polynomial.eval (Real.exp (-r)) Q - (w x - w (x - r))| ≤
        ε * (1 - Real.exp (-r)) +
          (if M < r then 2 * L * r else 0)) :
    ∀ t : ℝ≥0, t ≤ 1 →
      |∫ ω,
        (w x - w (x - ((t : ℝ) * X.drift - X.X t ω))) -
          Polynomial.eval (Real.exp (-((t : ℝ) * X.drift - X.X t ω))) Q ∂P| ≤
        ε * (∫ ω, (t : ℝ) * X.drift - X.X t ω ∂P) +
        2 * L * (∫ ω,
          if M < (t : ℝ) * X.drift - X.X t ω
          then (t : ℝ) * X.drift - X.X t ω else 0 ∂P) := by
  intro t ht
  let R : Ω → ℝ := fun ω => (t : ℝ) * X.drift - X.X t ω
  have hRm : Measurable R :=
    measurable_const.sub ((X.adapted t).mono (𝓕.le _) le_rfl)
  have hRnn : ∀ᵐ ω ∂P, 0 ≤ R ω := by
    filter_upwards [bv_actual_levy_residual_ae_monotone_all_times X hBV]
      with ω hm
    have h0 := hm (show (0 : ℝ≥0) ≤ t from bot_le)
    simpa [R, X.X_zero] using h0
  have hRi : Integrable R P :=
    avram_wave5_04c_actual_bv_residual_integrable_upto_one X hX hBV t ht
  have hTI : Integrable (fun ω => if M < R ω then R ω else 0) P :=
    avram_wave5_04c_actual_bv_residual_tail_integrable_upto_one X hX hBV t ht M
  have hf : Continuous (fun r : ℝ => w x - w (x - r)) :=
    continuous_const.sub (hw.continuous.comp (continuous_const.sub continuous_id))
  have hQpoint (r : ℝ) (hr : 0 ≤ r) :
      |Polynomial.eval (Real.exp (-r)) Q - (w x - w (x - r))| ≤
        ε * (1 - Real.exp (-r)) +
          (if M < r then (2 * L) * r else 0) := by
    simpa only [mul_assoc] using hpoint r hr
  simpa only [R] using
    (avram_wave5_04c_random_BV_weighted_polynomial_L1_error
      P R hRm hRnn hRi M ε (2 * L) hε (by positivity) hTI
      (fun r => w x - w (x - r)) hf Q hQpoint)
