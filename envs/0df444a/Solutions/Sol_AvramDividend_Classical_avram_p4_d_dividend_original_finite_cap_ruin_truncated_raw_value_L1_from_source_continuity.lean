-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_finite_cap_ruin_truncated_raw_value_L1_from_source_continuity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T23:41:17.431419+00:00
-- url     : https://prove2.me/submissions/75b6c6e4-37ee-4dab-b6e7-37cbef97a447

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_continuous_candidate_compact_cap_interval_bounded
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_finite_cap_linear_extension_global_exponential_envelope_of_interior_bound
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_ruin_truncated_raw_caplinear_value_L1_of_exp_envelope
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04b_cap_extension_measurable_of_zero_negative

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual finite-cap original comparison value is L1 at the ruin clock,
without introducing an additional global growth assumption. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hCfin : C ≠ ⊤)
    (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ z : ℝ, z < 0 → w z = 0)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z else
        w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω : Ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hXstopped : Measurable (fun ω => X.X (τ ω) ω)) :
    Integrable (fun ω => V (x + X.X (τ ω) ω)) P := by
  obtain ⟨M, hM, hBound⟩ :=
    avram_p4_d_dividend_original_continuous_candidate_compact_cap_interval_bounded
      C w hw_cont
  have hVmeas : Measurable V :=
    avram_wave6_04b_cap_extension_measurable_of_zero_negative
      w V C hw_cont hw_neg hVtop hVfinite
  have hEnvelope : ∀ z : ℝ, ‖V z‖ ≤ (M+1) * Real.exp z :=
    avram_p4_d_dividend_finite_cap_linear_extension_global_exponential_envelope_of_interior_bound
      C hCfin w V hw_neg hVfinite M hM hBound
  exact avram_p4_d_dividend_original_ruin_truncated_raw_caplinear_value_L1_of_exp_envelope
    X x D n τ hτeq hτmeas hτstop V hVmeas hXstopped
    (M+1) (by linarith) hEnvelope
