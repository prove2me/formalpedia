-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_02a_original_predictable_kernel_measurable_of_source_sfinite_kernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:27:58.847615+00:00
-- url     : https://prove2.me/submissions/b6ec6c26-0378-4682-b872-1c0ed95463d9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_original_predictable_sample_mark_lift_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (κ : Kernel Ω (ℝ≥0 × ℝ)) [IsSFiniteKernel κ]
    (hκ : ∀ ω, κ ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ 𝓕.predictable
        (inferInstance : MeasurableSpace ℝ)))
    (hK : ∀ ω, K ω =
      @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
        (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
        (@Prod.instMeasurableSpace _ _ 𝓕.predictable
          (inferInstance : MeasurableSpace ℝ))
        (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) (κ ω))
    (hJoint : @Measurable ((ℝ≥0 × ℝ) × Ω) ((ℝ≥0 × Ω) × ℝ)
      (inferInstance : MeasurableSpace ((ℝ≥0 × ℝ) × Ω))
      (@Prod.instMeasurableSpace _ _ 𝓕.predictable
        (inferInstance : MeasurableSpace ℝ))
      (fun q : (ℝ≥0 × ℝ) × Ω => ((q.1.1, q.2), q.1.2))) :
    AEMeasurable K P := by
  apply Measurable.aemeasurable
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have hInd : Measurable (Function.uncurry
      (fun p : ℝ≥0 × ℝ => fun ω : Ω =>
        s.indicator (fun _ => (1 : ℝ≥0∞)) ((p.1, ω), p.2))) :=
    (measurable_const.indicator hs).comp hJoint
  have hEval := Measurable.lintegral_kernel_prod_left (κ := κ) hInd
  convert hEval using 1
  funext ω
  rw [hK ω, Measure.map_apply
    (avram_wave5_p1_original_predictable_sample_mark_lift_measurable 𝓕 ω) hs]
  rw [← lintegral_indicator_one]
  congr 1
  exact (avram_wave5_p1_original_predictable_sample_mark_lift_measurable 𝓕 ω) hs
