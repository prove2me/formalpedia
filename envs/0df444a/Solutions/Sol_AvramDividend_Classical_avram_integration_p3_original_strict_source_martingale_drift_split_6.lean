-- Prove2me | solution 6 for AvramDividend.Classical.avram_integration_p3_original_strict_source_martingale_drift_split
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T17:13:59.247205+00:00
-- url     : https://prove2.me/submissions/b114abe8-6d0d-41b9-92b1-125e87fff22a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_strict_prefix_margin_sequence
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_cash_prefix_positive_F_and_fatou
import Theorems.Thm_AvramDividend_Classical_avram_bvb_original_BV_every_inner_horizon_expected_cash_terminal_le
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_reward_L1_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_signed_strict_fatou_real_grid_certificate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
/- The actual BV top-cap full-T stopped cash and prepayment survivor
   terminal from physical strict grid via kernel-proved Fatou. -/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T) :
    ∃ M B : Ω → ℝ,
      (Integrable M P ∧ (∫ ω, M ω ∂P) = 0) ∧
      (Integrable B P ∧ (∫ ω, B ω ∂P) ≤ 0) ∧
      (∀ᵐ ω ∂P,
        let S : ℝ≥0 := ⟨T, hT⟩
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
          (if (S : ℝ≥0∞) < ruinTime X x D ω then
            Real.exp (-(q * T)) * w (riskProcess X x D S ω)
          else 0) ≤ w x + M ω + B ω) := by
  classical
  let S : ℝ≥0 := ⟨T, hT⟩
  letI : IsProbabilityMeasure P := X.isProbability
  let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
  let term : Ω → ℝ := fun ω =>
    if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0
  let F : ℕ → Ω → ℝ := fun n ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      term ω
  let Y : Ω → ℝ := fun ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      term ω
  obtain ⟨hδpos, hδle, hδanti, hδlim⟩ :=
    avram_p3_grid3_strict_prefix_margin_sequence T hTpos
  obtain ⟨hF, hFatou⟩ :=
    avram_p3_grid4_original_cash_prefix_positive_F_and_fatou
      X hBV x C D hD w hw_cont hw_neg q hq.le T hTpos hw_nonneg
      δ hδpos hδle hδanti hδlim
  have hMean : ∀ n, (∫ ω, F n ω ∂P) ≤ w x := by
    intro n
    simpa only [F, δ, term, S] using
      (avram_bvb_original_BV_every_inner_horizon_expected_cash_terminal_le
        X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
        hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hTpos n)
  have hYPair := avram_p3_bv_original_strict_reward_L1_nonnegative
    X hBV x C D hD w hw_cont hw_neg q hq.le T hT hTpos hw_nonneg
  have hYInt : Integrable Y P := hYPair.1
  have hYNonneg : ∀ ω, 0 ≤ Y ω := hYPair.2
  have hwx : 0 ≤ w x :=
    (integral_nonneg (hF 0).2.2).trans (hMean 0)
  let Fe : ℕ → Ω → ℝ≥0∞ := fun n ω => ENNReal.ofReal (F n ω)
  have hFeMeas : ∀ n, Measurable (Fe n) := by
    intro n; exact ENNReal.measurable_ofReal.comp (hF n).1
  have hFeMean : ∀ n, (∫⁻ ω, Fe n ω ∂P) ≤ ENNReal.ofReal (w x) := by
    intro n
    change (∫⁻ ω, ENNReal.ofReal (F n ω) ∂P) ≤ ENNReal.ofReal (w x)
    rw [← ofReal_integral_eq_lintegral_ofReal (hF n).2.1
      (Filter.Eventually.of_forall (hF n).2.2)]
    exact ENNReal.ofReal_le_ofReal (hMean n)
  have hFatouAe : ∀ᵐ ω ∂P, ENNReal.ofReal (Y ω) ≤
      liminf (fun n => Fe n ω) atTop :=
    Filter.Eventually.of_forall hFatou
  have hYEnn : (∫⁻ ω, ENNReal.ofReal (Y ω) ∂P) ≤ ENNReal.ofReal (w x) :=
    avram_limit2_original_signed_strict_fatou_real_grid_certificate
      X q x T D term Fe (ENNReal.ofReal (w x)) hFeMeas hFeMean hFatouAe
  have hOfReal : ENNReal.ofReal (∫ ω, Y ω ∂P) ≤ ENNReal.ofReal (w x) := by
    rwa [ofReal_integral_eq_lintegral_ofReal hYInt
      (Filter.Eventually.of_forall hYNonneg)]
  have hReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hOfReal
  have hz : 0 ≤ (∫ ω, Y ω ∂P) := integral_nonneg hYNonneg
  have hBudget : (∫ ω, Y ω ∂P) ≤ w x := by
    simpa only [ENNReal.toReal_ofReal hz, ENNReal.toReal_ofReal hwx] using hReal
  let B : Ω → ℝ := fun ω => Y ω - w x
  have hBI : Integrable B P := hYInt.sub (integrable_const _)
  have hBmean : (∫ ω, B ω ∂P) ≤ 0 := by
    change (∫ ω, Y ω - w x ∂P) ≤ 0
    rw [integral_sub hYInt (integrable_const _)]
    simpa using sub_nonpos.mpr hBudget
  refine ⟨(fun _ => 0), B, ?_, ?_, ?_⟩
  · simp
  · exact ⟨hBI, hBmean⟩
  · filter_upwards [] with ω
    change Y ω ≤ w x + 0 + B ω
    simp [B]
