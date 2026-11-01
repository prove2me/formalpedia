-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_controlled_prejump_cap_gradient_stronglyPredictable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T19:33:44.873796+00:00
-- url     : https://prove2.me/submissions/86014248-409a-4157-9f42-dbeff2ae37ea

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_measurable_cap_interior_deriv_zero_extension

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- A Borel cap-interior derivative of the actual pre-jump reserve is predictable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    IsStronglyPredictable 𝓕.rightCont
      (fun t ω =>
        let y := Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
        if 0 < y ∧ ENNReal.ofReal y < C then deriv w y else 0) := by
  have hpred :=
    avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable X x D hD
  have hderiv :=
    avram_wave4_04b_measurable_cap_interior_deriv_zero_extension w C hw
  unfold IsStronglyPredictable at hpred ⊢
  exact (hderiv.comp hpred.measurable).stronglyMeasurable
