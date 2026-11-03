-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_chat09_original_bv_bounded_clock_closed_horizon_drift_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T09:45:45.600756+00:00
-- url     : https://prove2.me/submissions/32eb3133-90b0-4a80-839b-883cf194988a

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_complete_closed_horizon_expected_drift_budget

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (x : ℝ) (hx : 0 ≤ x) (C : ℝ≥0∞)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτBound : ∀ ω, τ ω ≤ T) :
    (∫⁻ ω, ∫⁻ t in
      paymentTimes (ruinTime X x D ω) ∩ Iic ((τ ω : ℝ≥0) : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal
        (x + (((T + 1 : ℝ≥0) : ℝ) * X.drift)) := by
  have hTH : T < T + 1 := by
    exact lt_add_of_pos_right T (by norm_num : (0 : ℝ≥0) < 1)
  have hσReal (ω : Ω) : ((τ ω : ℝ≥0) : ℝ) ≤ (T : ℝ) := by
    exact_mod_cast hτBound ω
  have hsub (ω : Ω) :
      paymentTimes (ruinTime X x D ω) ∩ Iic ((τ ω : ℝ≥0) : ℝ) ⊆
        paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ) := by
    intro t ht
    exact ⟨ht.1, le_trans ht.2 (hσReal ω)⟩
  have hpath (ω : Ω) :
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Iic ((τ ω : ℝ≥0) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) :=
    lintegral_mono_set (hsub ω)
  exact (lintegral_mono hpath).trans
    (avram_wave3_03_bv_complete_closed_horizon_expected_drift_budget
      X hX hBV x hx C hxc D hD q hq T (T + 1) hTH)
