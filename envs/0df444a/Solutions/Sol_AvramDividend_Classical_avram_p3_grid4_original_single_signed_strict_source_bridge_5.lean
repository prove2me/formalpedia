-- Prove2me | solution 5 for AvramDividend.Classical.avram_p3_grid4_original_single_signed_strict_source_bridge
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T17:24:30.467742+00:00
-- url     : https://prove2.me/submissions/af210103-af2e-45c2-a171-2bc3d8bc9202
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_original_uniform_physical_nol1_cell_certificate
import Theorems.Thm_AvramDividend_Classical_avram_redux9_original_uniform_grid_total_B_ae_nonpositive
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_original_nonintegrable_B_vanishing_error_budget
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_original_physical_prefix_cofinal_clock
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_source_witness_from_strict_mean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/- The actual uniform BV source has nonpositive drift B without an
   integrability obligation, allowing the original strict clock Fatou budget. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (hX : X.Standing)
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
    ∃ Z : Ω → ℝ,
      Integrable Z P ∧ (∫ ω, Z ω ∂P) ≤ 0 ∧
      (∀ᵐ ω ∂P,
        let S : ℝ≥0 := ⟨T, hT⟩
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
        else 0) ≤ w x + Z ω) := by
  let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
  let v : ℕ → ℝ := fun n => T - δ n
  let S : ℝ≥0 := ⟨T, hT⟩
  rcases avram_bv_strict6_original_uniform_physical_nol1_cell_certificate
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad
      x hx hxc D hD hw_nonneg hjump T hTpos with
    ⟨u, M, B, Err, hgrid, hmono, huniform, hBexact,
      hMI, hErrInt, hErrMean, hPhysical⟩
  have hBglobal : ∀ᵐ ω ∂P, ∀ n, B n ω ≤ 0 :=
    avram_redux9_original_uniform_grid_total_B_ae_nonpositive
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad
      x hx hxc D hD hw_nonneg hjump T hTpos
      u hgrid hmono huniform B hBexact
  have hB : ∀ n, ∀ᵐ ω ∂P, B n ω ≤ 0 := by
    intro n
    filter_upwards [hBglobal] with ω hω
    exact hω n
  have hM : ∀ n, Integrable (M n) P ∧
      (∫ ω, M n ω ∂P) ≤ 0 := by
    intro n
    exact ⟨(hMI n).1, le_of_eq (hMI n).2⟩
  have hClock := avram_bv_strict6_original_physical_prefix_cofinal_clock T hTpos
  change Monotone v ∧ (∀ n, 0 ≤ v n) ∧ (∀ n, v n ≤ T) ∧
    (∀ s : ℝ, s < T → ∃ n, s < v n) at hClock
  rcases hClock with ⟨hvmono, hvnonneg, hvbelow, hvcover⟩
  have hPhysicalV (n : ℕ) : ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (v n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0) ≤ w x + (M n ω + B n ω) + max (Err n ω) 0 := by
    simpa [v, δ] using hPhysical n
  have hBudget :
      (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
        else 0) ∂P) ≤ w x := by
    exact avram_bv_strict6_original_nonintegrable_B_vanishing_error_budget
      X hBV x C D hD w hw_cont hw_neg q (le_of_lt hq)
      S v hvmono hvnonneg hvbelow hvcover M B Err
      hM hB hErrInt hErrMean hPhysicalV
  exact avram_p3_bv_original_source_witness_from_strict_mean
    X hBV x C D hD w hw_cont hw_neg q (le_of_lt hq) T hT hBudget
