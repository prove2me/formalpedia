-- Prove2me | solution 2 for AvramDividend.Classical.avram_bva41_all_activity_physical_prefix_expected_budget_nonL1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T01:23:12.252428+00:00
-- url     : https://prove2.me/submissions/6394b473-3a81-4da3-83bc-8c28ab53b1e5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva42_uniform_physical_grid_canonical
import Theorems.Thm_AvramDividend_Classical_avram_bvb_original_uniform_grid_exists_exact_B_nonpositive_and_true_prepayment
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict10_original_two_scale_cell_contact_no_meas
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict11_uniform_B_source_to_strict_expected_upper
import Theorems.Thm_AvramDividend_Classical_avram_bva46_original_strict_cash_prefix_pointwise_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_prebudget_L1
import Theorems.Thm_AvramDividend_Classical_avram_bvb62_original_all_cap_strict_cash_plus_full_T_terminal_integrable
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

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
    (T : ℝ) (hT : 0 < T)
    :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    ∀ n : ℕ, (∫ ω, F n ω ∂P) ≤ w x := by
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨u, hgrid, hu, huniform⟩ :=
    avram_bva42_uniform_physical_grid_canonical T hT
  have hmono : ∀ m i, i < m + 1 → u m i ≤ u m (i + 1) := by
    intro m i _
    exact hu m i
  obtain ⟨B, hB, _, _⟩ :=
    avram_bvb_original_uniform_grid_exists_exact_B_nonpositive_and_true_prepayment
      X hX hBV q w C hw_gen x D hD.1.1 T hT u hu huniform
  have hSource :=
    avram_bv_strict10_original_two_scale_cell_contact_no_meas
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      T hT u hgrid hmono huniform B hB
  intro δ S F n
  let Y : Ω → ℝ := fun ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
    (if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
  have hYI : Integrable Y P := by
    simpa only [Y, S] using
      (avram_p3_bv_original_prebudget_L1
        X hBV x C D hD w hw_cont hw_neg q hq.le T hT.le)
  have hFI : Integrable (F n) P := by
    simpa only [F, δ, S] using
      (avram_bvb62_original_all_cap_strict_cash_plus_full_T_terminal_integrable
        X hBV x C D hD w hw_cont hw_neg q hq T hT n)
  have hPrefix : ∀ ω, F n ω ≤ Y ω := by
    intro ω
    have hδ : 0 ≤ δ n := by dsimp [δ]; positivity
    have hc :=
      avram_bva46_original_strict_cash_prefix_pointwise_monotone
        X x C D hD q hq.le T hT (δ n) hδ ω
    simpa only [F, Y, add_comm] using add_le_add_right hc
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
  have hFullMean : (∫ ω, Y ω ∂P) ≤ w x := by
    simpa only [Y, S] using
      (avram_bv_strict11_uniform_B_source_to_strict_expected_upper
        X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
        hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
        T hT u hgrid hmono huniform B hB hSource)
  exact (integral_mono hFI hYI hPrefix).trans hFullMean
