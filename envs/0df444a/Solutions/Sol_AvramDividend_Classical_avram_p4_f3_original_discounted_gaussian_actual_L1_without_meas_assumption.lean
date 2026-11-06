-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_discounted_gaussian_actual_L1_without_meas_assumption
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T20:33:26.682723+00:00
-- url     : https://prove2.me/submissions/bc404ad0-4464-4415-a208-9ffc31a2e5e7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_discounted_gaussian_coefficient_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_discounted_gaussian_integrable_from_finite_energy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Fully original pathwise Gaussian coefficient has L1 on finite physical sources. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q)
    (δ K ε : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C) (hε : 0 < ε)
    (μ : Measure (ℝ≥0 × Ω)) (hμ : μ univ < ⊤) :
    let U : ℝ≥0 × Ω → ℝ := fun p =>
      let y := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
      if y ∈ Icc δ K then y else δ
    Integrable (fun p =>
      Real.exp (-(q * (p.1 : ℝ))) *
        (X.σ * deriv w (U p))) μ := by
  have hGm :=
    avram_p4_f3_original_discounted_gaussian_coefficient_measurable
      X x D hD w q δ K hδK
  exact
    avram_p4_f3_original_discounted_gaussian_integrable_from_finite_energy
      X x D w C hw_cont hw_neg hw_smooth q hq
      δ K ε hδ hδK hK hε μ hμ hGm.aestronglyMeasurable
