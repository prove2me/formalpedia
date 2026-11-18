-- Prove2me | solution 13 for AvramDividend.Classical.avram_p3_bv_original_source_signed_fatou_grid_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T17:27:29.311328+00:00
-- url     : https://prove2.me/submissions/c38aad13-6216-49f7-b58d-d08f6a9cd3dd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_strict_prefix_margin_sequence
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_cash_prefix_positive_F_and_fatou
import Theorems.Thm_AvramDividend_Classical_avram_bvb_original_BV_every_inner_horizon_expected_cash_terminal_le
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T) :
    ∃ F M B : ℕ → Ω → ℝ,
      (∀ n, Measurable (F n)) ∧
      (∀ n, Integrable (F n) P) ∧
      (∀ n, 0 ≤ᵐ[P] F n) ∧
      (∀ n, Integrable (fun ω => M n ω + B n ω) P ∧
        (∫ ω, M n ω + B n ω ∂P) ≤ 0) ∧
      (∀ n, ∀ᵐ ω ∂P,
        F n ω ≤ w x + (M n ω + B n ω)) ∧
      (∀ᵐ ω ∂P,
        let S : ℝ≥0 := ⟨T, hT⟩
        ENNReal.ofReal (
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
            ENNReal.ofReal (Real.exp (-(q * t)))
              ∂(dividendMeasure D ω)).toReal +
          (if (S : ℝ≥0∞) < ruinTime X x D ω then
            Real.exp (-(q * T)) * w (riskProcess X x D S ω)
          else 0)) ≤
        liminf (fun n => ENNReal.ofReal (F n ω)) atTop) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
  let S : ℝ≥0 := ⟨T, hT⟩
  let F : ℕ → Ω → ℝ := fun n ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
  obtain ⟨hδpos, hδle, hδanti, hδlim⟩ :=
    avram_p3_grid3_strict_prefix_margin_sequence T hTpos
  obtain ⟨hF, hFatou⟩ :=
    avram_p3_grid4_original_cash_prefix_positive_F_and_fatou
      X hBV x C D hD w hw_cont hw_neg q hq.le T hTpos hw_nonneg
      δ hδpos hδle hδanti hδlim
  have hMean : ∀ n, (∫ ω, F n ω ∂P) ≤ w x := by
    intro n
    simpa only [F, δ, S] using
      (avram_bvb_original_BV_every_inner_horizon_expected_cash_terminal_le
        X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
        hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hTpos n)
  refine ⟨F, (fun _ _ => 0), (fun n ω => F n ω - w x),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact (hF n).1
  · intro n
    exact (hF n).2.1
  · intro n
    exact Filter.Eventually.of_forall (hF n).2.2
  · intro n
    have hI : Integrable (fun ω => F n ω - w x) P := by
      convert (hF n).2.1.sub (integrable_const (w x)) using 1
      funext ω
      simp [F, S]
    constructor
    · change Integrable (fun ω => (0 : ℝ) + (F n ω - w x)) P
      simpa only [zero_add] using hI
    · have hBmean : (∫ ω, F n ω - w x ∂P) ≤ 0 := by
        rw [integral_sub (hF n).2.1 (integrable_const _)]
        simpa using sub_nonpos.mpr (hMean n)
      change (∫ ω, (0 : ℝ) + (F n ω - w x) ∂P) ≤ 0
      simpa only [zero_add] using hBmean
  · intro n
    filter_upwards [] with ω
    simp
  · filter_upwards [] with ω
    simpa only [F, δ, S] using hFatou ω
