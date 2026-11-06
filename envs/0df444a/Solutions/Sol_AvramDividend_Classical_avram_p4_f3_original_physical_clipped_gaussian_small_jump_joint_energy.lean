-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_physical_clipped_gaussian_small_jump_joint_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:51:40.405284+00:00
-- url     : https://prove2.me/submissions/e54c89b3-8216-49ee-92b3-5fb9a4eb69a7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_clipped_predividend_gaussian_gradient_finite_energy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_physical_clipped_predividend_negative_band_joint_L2_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Same physical clipped pre-dividend reserve simultaneously has Gaussian and jump finite quadratic energy. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ K ε : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C)
    (μ : Measure (ℝ≥0 × Ω)) (hμ : μ univ < ⊤) :
    let U : ℝ≥0 × Ω → ℝ := fun p =>
      let y := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
      if y ∈ Icc δ K then y else δ
    (∫⁻ p, ENNReal.ofReal ((X.σ * deriv w (U p)) ^ 2) ∂μ) < ⊤ ∧
    (∫⁻ p, (∫⁻ z in Ioo (-ε) (0 : ℝ),
      ENNReal.ofReal
        (((w (U p + z) - w (U p)) -
          (w (δ + z) - w δ)) ^ 2) ∂X.ν) ∂μ) < ⊤ := by
  constructor
  · exact
      avram_p4_f3_original_clipped_predividend_gaussian_gradient_finite_energy
        X x D w C hw_smooth δ K hδ hδK hK μ hμ
  · exact
      avram_p4_f3_original_physical_clipped_predividend_negative_band_joint_L2_finite
        X x D w C hw_cont hw_neg hw_smooth δ K ε hδ hδK hK μ hμ
