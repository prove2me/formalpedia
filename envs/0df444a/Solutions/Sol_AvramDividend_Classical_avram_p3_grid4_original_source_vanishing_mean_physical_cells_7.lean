-- Prove2me | solution 7 for AvramDividend.Classical.avram_p3_grid4_original_source_vanishing_mean_physical_cells
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T08:30:47.570329+00:00
-- url     : https://prove2.me/submissions/7f519342-065a-447c-a832-f06c5d85db49
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_original_canonical_strict_prefix_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_centered_gap_positive_error_aggregation
import Theorems.Thm_AvramDividend_Classical_avram_bvb_original_BV_uniform_expected_cash_terminal_positive_gap_vanishes

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Convert the original stopped expected positive budget to a same-probability-space
integrable centred physical certificate. The drift component can be chosen as zero. -/
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
    ∃ M B Err : ℕ → Ω → ℝ,
      (∀ n, Integrable (fun ω => M n ω + B n ω) P ∧
        (∫ ω, M n ω + B n ω ∂P) ≤ 0) ∧
      (∀ n, Integrable (fun ω => max (Err n ω) 0) P) ∧
      Tendsto (fun n => ∫ ω, max (Err n ω) 0 ∂P) atTop (𝓝 0) ∧
      (∀ n, ∀ᵐ ω ∂P,
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
          (if (S : ℝ≥0∞) < ruinTime X x D ω then
            Real.exp (-(q * T)) * w (riskProcess X x D S ω)
          else 0) ≤
        w x + (M n ω + B n ω) + max (Err n ω) 0) := by
  dsimp only
  let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
  let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
  let F : ℕ → Ω → ℝ := fun n ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
    (if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
  letI : IsProbabilityMeasure P := X.isProbability
  have hFI : ∀ n, Integrable (F n) P := by
    simpa only [F, δ, S] using
      (avram_p3_comp8_original_canonical_strict_prefix_integrable
        X hBV x C D hD w hw_cont hw_neg q hq T hT hw_nonneg)
  have hgap : Tendsto
      (fun n => max ((∫ ω, F n ω ∂P) - w x) 0) atTop (𝓝 0) := by
    simpa only [F, δ, S] using
      (avram_bvb_original_BV_uniform_expected_cash_terminal_positive_gap_vanishes
        X hX hBV q hq w C hC hw_cont hw0 hw_neg
        hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hT)
  let B : ℕ → Ω → ℝ := fun _ _ => 0
  have hBI : ∀ n, Integrable (B n) P := by
    intro n
    fun_prop
  have hgap' : Tendsto
      (fun n => max ((∫ ω, F n ω ∂P) - w x -
        (∫ ω, B n ω ∂P)) 0) atTop (𝓝 0) := by
    simpa only [B, integral_zero, sub_zero] using hgap
  obtain ⟨M, Err, hM, hErrI, hErrMean, hpath⟩ :=
    avram_p3_grid4_centered_gap_positive_error_aggregation
      F B (w x) hFI hBI hgap'
  refine ⟨M, B, Err, ?_, hErrI, hErrMean, ?_⟩
  · intro n
    obtain ⟨hMI, hM0⟩ := hM n
    constructor
    · simpa only [B, add_zero] using hMI
    · simpa only [B, add_zero] using (le_of_eq hM0)
  · intro n
    filter_upwards [] with ω
    simpa only [F, δ, S] using hpath n ω
