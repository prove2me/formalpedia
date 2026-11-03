-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_intrinsic_future_borel_mark_void_event_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:26:36.86789+00:00
-- url     : https://prove2.me/submissions/0c309ce6-3818-49ca-825a-3d808445b99e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_shifted_future_path_coordinate_product_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Literal source future marked-jump voids form measurable events because
they are the preimage of zero under the same-path measurable extractor. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) :
    MeasurableSet {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ B) = 0} := by
  obtain ⟨F, hFm, hFrep⟩ :=
    avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
      X s t hst B hB
  have hShift :
      Measurable (fun ω : Ω =>
        fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω) :=
    avram_wave7_01_original_shifted_future_path_coordinate_product_measurable
      X s
  have hCount : Measurable (fun ω : Ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ B)) := by
    have hFcomp := hFm.comp hShift
    convert hFcomp using 1
    funext ω
    exact hFrep ω
  exact (measurableSet_singleton (0 : ℝ≥0∞)).preimage hCount
