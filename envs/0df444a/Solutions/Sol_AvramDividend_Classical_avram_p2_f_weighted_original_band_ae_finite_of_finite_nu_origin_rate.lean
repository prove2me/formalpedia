-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_original_band_ae_finite_of_finite_nu_origin_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T16:13:37.19795+00:00
-- url     : https://prove2.me/submissions/7b219776-9ae8-4189-bc4f-c61d9d8e6dfc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_rectangle_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_band_l1_of_finite_nu_origin_rate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Finite original source ν mark mass and finite past-weight first moment
force the genuine marked future weighted count to be finite a.s. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (H : Ω → ℝ≥0∞) (hH : Measurable[𝓕 s] H)
    (hOrigin : (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B) ∂P) = ((T : ℝ≥0∞) * X.ν B))
    (hHfinite : (∫⁻ ω, H ω ∂P) ≠ ∞)
    (hνfinite : X.ν B ≠ ∞) :
    ∀ᵐ ω ∂P, H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B) < ∞ := by
  have hHmeas : Measurable H := hH.mono (𝓕.le s) le_rfl
  have hNmeas : Measurable (fun ω => ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B)) :=
    avram_p2_f_weighted_original_intrinsic_rectangle_measurable X s T B hB
  exact MeasureTheory.ae_lt_top (hHmeas.mul hNmeas)
    (avram_p2_f_weighted_original_band_l1_of_finite_nu_origin_rate
      X s T B hB H hH hOrigin hHfinite hνfinite)
