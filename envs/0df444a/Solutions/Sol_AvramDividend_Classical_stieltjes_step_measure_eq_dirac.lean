-- Prove2me | solution 1 for AvramDividend.Classical.stieltjes_step_measure_eq_dirac
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T02:59:58.042327+00:00
-- url     : https://prove2.me/submissions/28a684b8-cada-4ec1-b0e5-874eeca243b5

import Mathlib

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

open MeasureTheory Filter Set Topology in
theorem solution (d : ℝ) (hd : 0 ≤ d)
    (hf : Monotone (fun t : ℝ => if t < 0 then 0 else d)) :
    hf.stieltjesFunction.measure =
      (ENNReal.ofReal d) • (Measure.dirac (0 : ℝ)) := by
  have hF : ∀ x : ℝ, hf.stieltjesFunction x = if x < 0 then 0 else d := by
    intro x
    rw [Monotone.stieltjesFunction_eq]
    apply rightLim_eq_of_tendsto
    by_cases hx : x < 0
    · simp only [hx, if_true]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT hx] with y hy
      simp [hy.2]
    · simp only [hx, if_false]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with y (hy : x < y)
      have : ¬ y < 0 := not_lt.mpr ((not_lt.mp hx).trans hy.le)
      simp [this]
  refine Measure.ext_of_Ioc _ _ (fun a b hab => ?_)
  rw [StieltjesFunction.measure_Ioc, hF, hF, Measure.smul_apply,
    Measure.dirac_apply' _ measurableSet_Ioc, smul_eq_mul]
  by_cases ha : a < 0
  · by_cases hb : b < 0
    · have h0 : (0 : ℝ) ∉ Ioc a b := fun h => absurd h.2 (not_le.mpr hb)
      simp [ha, hb, h0]
    · have h0 : (0 : ℝ) ∈ Ioc a b := ⟨ha, not_lt.mp hb⟩
      simp [ha, hb, h0]
  · have hb : ¬ b < 0 := not_lt.mpr ((not_lt.mp ha).trans hab.le)
    have h0 : (0 : ℝ) ∉ Ioc a b := fun h => ha h.1
    simp [ha, hb, h0]
