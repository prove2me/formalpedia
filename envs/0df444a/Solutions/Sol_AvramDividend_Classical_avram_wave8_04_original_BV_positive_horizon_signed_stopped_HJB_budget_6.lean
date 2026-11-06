-- Prove2me | solution 6 for AvramDividend.Classical.avram_wave8_04_original_BV_positive_horizon_signed_stopped_HJB_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T00:16:41.515145+00:00
-- url     : https://prove2.me/submissions/33f65207-b089-4078-b51a-4c7f3ddaca5d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_redux3_bv_original_cofinal_strict_mesh_expected_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_stopped_strict_mean_budget_of_cofinal_C1_mesh
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_source_witness_from_strict_mean
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_strict_residual_to_signed_horizon

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
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
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T) :
    let S : ℝ≥0 := ⟨T,hT⟩
    let Term : Ω → ℝ := fun ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) *
          w (x + X.X S ω - rightLimit D S ω)
      else 0
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) +
      (∫ ω, Term ω ∂P) ≤ w x := by
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨u, hmono, hu, hlt, hcover, hMesh⟩ :=
    avram_redux3_bv_original_cofinal_strict_mesh_expected_budget
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad
      x hx hxc D hD hw_nonneg hjump T hT hTpos
  have hMean :=
    avram_p3_f2_original_stopped_strict_mean_budget_of_cofinal_C1_mesh
      X hBV x C D hD w hw_cont hw_neg q (le_of_lt hq)
      ⟨T, hT⟩ u hmono hu (fun n => le_of_lt (hlt n))
      hcover (w x) hMesh
  obtain ⟨E, hEInt, hEMean, hStrict⟩ :=
    avram_p3_bv_original_source_witness_from_strict_mean
      X hBV x C D hD w hw_cont hw_neg
      q (le_of_lt hq) T hT hMean
  exact avram_p3_2_original_strict_residual_to_signed_horizon
    X hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_grad
    x hx hxc D hD hjump T hT hTpos E hEInt hEMean hStrict
