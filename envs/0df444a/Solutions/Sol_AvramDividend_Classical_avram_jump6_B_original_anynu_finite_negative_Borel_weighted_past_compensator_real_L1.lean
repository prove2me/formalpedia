-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_anynu_finite_negative_Borel_weighted_past_compensator_real_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T10:07:29.619514+00:00
-- url     : https://prove2.me/submissions/ceeb4bcb-79b2-41b2-b26c-4142ac090f5d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_negative_Borel_marked_Poisson_interval_Campbell_exact
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_signed_past_weighted_real_rate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (Wpos Wneg : Ω → ℝ≥0∞)
    (hWpos : Measurable[𝓕 s] Wpos)
    (hWneg : Measurable[𝓕 s] Wneg)
    (hPosFinite : (∫⁻ ω, Wpos ω ∂P) < ⊤)
    (hNegFinite : (∫⁻ ω, Wneg ω ∂P) < ⊤)
    (hν : X.ν B < ⊤)
    (hNeg : B ⊆ Iio (0 : ℝ)) :
    Integrable (fun ω =>
      (Wpos ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal -
      (Wneg ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal) P ∧
    (∫ ω,
      (Wpos ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal -
      (Wneg ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal ∂P) =
      ((∫⁻ ω, Wpos ω ∂P) * (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)).toReal -
      ((∫⁻ ω, Wneg ω ∂P) * (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)).toReal := by
  have hRate :=
    avram_b24_original_negative_Borel_marked_Poisson_interval_Campbell_exact
      X s t hst B hB hNeg
  exact avram_p2_e_compensator_signed_past_weighted_real_rate
    X s t hst B hB Wpos Wneg hWpos hWneg hPosFinite hNegFinite hν hRate
