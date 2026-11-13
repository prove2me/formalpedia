-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_physical_clock_endpoint_fiber_zero_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T19:17:54.191212+00:00
-- url     : https://prove2.me/submissions/8bc1ccf7-8d58-427a-87ee-0843e616da60

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    (T : ℝ) (t : ℝ≥0) (f : ℝ≥0 → ℝ) :
    let μ : Measure ℝ≥0 := (((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)
    (∫ s, if s = t then f s else 0 ∂μ) = 0 := by
  classical
  intro μ
  have hm : Measurable Real.toNNReal := continuous_real_toNNReal.measurable
  have hzero : μ {t} = 0 := by
    change (((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal) {t} = 0
    rw [Measure.map_apply hm (measurableSet_singleton t),
      Measure.restrict_apply ((measurableSet_singleton t).preimage hm)]
    apply measure_mono_null ?_ (measure_singleton (t : ℝ))
    intro r hr
    have heq : Real.toNNReal r = t := hr.1
    rw [Real.toNNReal_of_nonneg hr.2.1] at heq
    exact congrArg (fun z : ℝ≥0 => (z : ℝ)) heq
  have hae : ∀ᵐ s ∂μ, s ≠ t := by
    rw [ae_iff]
    simpa using hzero
  apply integral_eq_zero_of_ae
  filter_upwards [hae] with s hs
  simp [hs]
