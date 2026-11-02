-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_01_actual_source_prejump_mark_kernel_raw_predictable_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:12:46.149392+00:00
-- url     : https://prove2.me/submissions/b413d21b-14bd-4af1-9036-6f8ed43b4f95

import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_prejump_predictable_raw_original_filtration

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (F : ℝ × ℝ → ℝ) (hF : Measurable F) :
    Measurable[(@Prod.instMeasurableSpace _ _ (𝓕.predictable)
      (inferInstance : MeasurableSpace ℝ))]
      (fun p : ((ℝ≥0 × Ω) × ℝ) =>
        F (Function.leftLim
          (fun u : ℝ≥0 => X.X u p.1.2) p.1.1, p.2)) := by
  have hPre : Measurable[𝓕.predictable]
      (fun q : ℝ≥0 × Ω =>
        Function.leftLim (fun u : ℝ≥0 => X.X u q.2) q.1) := by
    exact (avram_wave5_01_actual_source_prejump_predictable_raw_original_filtration X).measurable
  have hPreLift :
      Measurable[(@Prod.instMeasurableSpace _ _
        (𝓕.predictable) (inferInstance : MeasurableSpace ℝ))]
        (fun p : (ℝ≥0 × Ω) × ℝ =>
          Function.leftLim (fun u : ℝ≥0 => X.X u p.1.2) p.1.1) :=
    hPre.comp measurable_fst
  exact hF.comp (hPreLift.prodMk measurable_snd)
