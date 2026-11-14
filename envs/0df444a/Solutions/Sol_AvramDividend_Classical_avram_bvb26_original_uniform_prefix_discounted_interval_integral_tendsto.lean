-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb26_original_uniform_prefix_discounted_interval_integral_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:57:12.257199+00:00
-- url     : https://prove2.me/submissions/cf1d6c92-e5d3-4c77-ab00-892fd133e299

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    (q T : ℝ) (hT : 0 < T) :
    Tendsto (fun n : ℕ =>
      ∫ t in (0 : ℝ)..(T - T / ((n : ℝ) + 2)),
        Real.exp (-(q * t)) ∂(volume : Measure ℝ))
      atTop (𝓝 (∫ t in (0 : ℝ)..T,
        Real.exp (-(q * t)) ∂(volume : Measure ℝ)))  := by
  have hf : Continuous (fun t : ℝ => Real.exp (-(q * t))) := by
    fun_prop
  have hPrimitive : Continuous (fun b : ℝ =>
      ∫ t in (0 : ℝ)..b, Real.exp (-(q * t)) ∂(volume : Measure ℝ)) :=
    intervalIntegral.continuous_primitive
      (fun a b => hf.intervalIntegrable a b) 0
  have hDiv : Tendsto (fun n : ℕ => T / ((n : ℝ) + 2))
      atTop (𝓝 (0 : ℝ)) := by
    have hShift :=
      (Filter.tendsto_add_atTop_iff_nat
        (f := fun n : ℕ => T / (n : ℝ))
        (l := 𝓝 (0 : ℝ)) 2).2
        (tendsto_const_div_atTop_nhds_zero_nat T)
    simpa [Nat.cast_add] using hShift
  have hEnd : Tendsto (fun n : ℕ => T - T / ((n : ℝ) + 2))
      atTop (𝓝 T) := by
    simpa using (tendsto_const_nhds.sub hDiv)
  exact hPrimitive.continuousAt.tendsto.comp hEnd
