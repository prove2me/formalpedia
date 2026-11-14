-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB248_continuous_minus_locally_BV_reserve_ae_time_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T11:30:59.844748+00:00
-- url     : https://prove2.me/submissions/d86f2a10-f967-412e-9a0d-c32be3587b60

import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB247_continuous_source_minus_BV_discontinuities_countable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Countability of reserve time discontinuities gives ae continuity under any atomless time measure. -/
theorem solution
    (f : ℝ≥0 → ℝ) (hf : Continuous f)
    (d : ℝ≥0 → ℝ)
    (hd : LocallyBoundedVariationOn d Set.univ)
    (x : ℝ) (μ : Measure ℝ≥0) [NullSingletonClass μ] :
    ∀ᵐ t ∂μ, ContinuousAt
      (fun s : ℝ≥0 => x + f s - d s) t := by
  have hc : Set.Countable {t : ℝ≥0 |
      ¬ ContinuousAt (fun s : ℝ≥0 => x + f s - d s) t} :=
    avram_gbB247_continuous_source_minus_BV_discontinuities_countable
      f hf d hd x
  have hNull := hc.measure_zero μ
  exact ae_iff.mpr hNull
