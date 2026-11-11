-- Prove2me | solution 2 for AvramDividend.Classical.avram_bvb_original_BV_uniform_expected_cash_terminal_positive_gap_vanishes
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T09:42:36.175551+00:00
-- url     : https://prove2.me/submissions/2f41b5be-04ff-4b57-9652-9293ece8fd38
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_uniform_B_full_source
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict10_original_two_scale_cell_contact_source
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict10_two_scale_signed_expected_upper
import Theorems.Thm_AvramDividend_Classical_avram_a19_uniform_delta_profile
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_cash_prefix_positive_F_and_fatou

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The source two-scale mesh certificate suffices for the original
expected positive-gap limit, with no raw-generator L1 assumption. -/
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
    (T : ℝ) (hT : 0 < T) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    Tendsto (fun n => max ((∫ ω, F n ω ∂P) - w x) 0)
      atTop (𝓝 (0 : ℝ)) := by
  dsimp only
  letI : IsProbabilityMeasure P := X.isProbability
  let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
  let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
  let F : ℕ → Ω → ℝ := fun n ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
    (if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
  have hSource := avram_p3_grid4_original_uniform_B_full_source
    X hBV q w C hw_gen hw_grad x D T hT
  dsimp only at hSource
  obtain ⟨u, B, hgrid, hmono, huniform, hB, hBneg⟩ := hSource
  have hTwo := avram_bv_strict10_original_two_scale_cell_contact_source
    X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen
    hw_grad x hx hxc D hD hw_nonneg hjump T hT
    u hgrid hmono huniform B hB
  dsimp only at hTwo
  obtain ⟨M, E1, E2, η, hηpos, hηzero, hM, hE1, hE2,
    hExcess, hBudget, hPick⟩ := hTwo
  have hDelta := avram_a19_uniform_delta_profile T hT
  dsimp only at hDelta
  obtain ⟨hδpos, hδle, hδanti, hδzero⟩ := hDelta
  have hPay := avram_p3_grid4_original_cash_prefix_positive_F_and_fatou
    X hBV x C D hD w hw_cont hw_neg q (le_of_lt hq) T hT
    hw_nonneg δ hδpos hδle hδanti hδzero
  dsimp only at hPay
  have hFmeas : ∀ n, AEStronglyMeasurable (F n) P := by
    intro n
    exact (hPay.1 n).1.aestronglyMeasurable
  have hFnonneg : ∀ n, ∀ᵐ ω ∂P, 0 ≤ F n ω := by
    intro n
    exact Filter.Eventually.of_forall (hPay.1 n).2.2
  have hEventually : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, (∫ ω, F n ω ∂P) ≤ w x + ε :=
    (avram_bv_strict10_two_scale_signed_expected_upper
      P F B M E1 E2 η (w x)
      (fun n k => (hM n k).1)
      (fun n k => (hM n k).2)
      hE1 hE2 hFmeas hFnonneg hBneg hBudget hηzero hPick).2
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall (fun n =>
      lt_of_lt_of_le ha (le_max_right _ _))
  · intro a ha
    have hhalf : 0 < a / 2 := by linarith
    filter_upwards [hEventually (a / 2) hhalf] with n hn
    have hdiff : (∫ ω, F n ω ∂P) - w x ≤ a / 2 := by linarith
    have hmax : max ((∫ ω, F n ω ∂P) - w x) 0 ≤ a / 2 :=
      max_le hdiff (le_of_lt hhalf)
    linarith
