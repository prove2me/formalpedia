-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_05_killed_mesh_fatou_lower_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T10:32:39.536203+00:00
-- url     : https://prove2.me/submissions/d1805f50-1703-4274-b582-f4eb8591b951

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_killed_right_mesh_discount_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_killed_right_mesh_discount_measurable
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology
open scoped ENNReal Classical

/-- Fatou's inequality compares the strictly killed continuous-time discounted
payment weight to right-endpoint sampled weights under any Stieltjes measure. -/
theorem solution (μ : Measure ℝ) (q : ℝ) (τ : ℝ≥0∞) :
    (∫⁻ r : ℝ, if 0 < r then
      if ENNReal.ofReal r < τ then
        ENNReal.ofReal (Real.exp (-(q * r))) else 0
      else 0 ∂μ) ≤
    liminf (fun n : ℕ =>
      ∫⁻ r : ℝ, if 0 < r then
        let e := ((⌈r * ((n : ℝ) + 1)⌉ : ℤ) : ℝ) / ((n : ℝ) + 1)
        if ENNReal.ofReal e < τ then
          ENNReal.ofReal (Real.exp (-(q * e))) else 0
        else 0 ∂μ) atTop := by
  let f : ℕ → ℝ → ℝ≥0∞ := fun n r =>
    if 0 < r then
      let e := ((⌈r * ((n : ℝ) + 1)⌉ : ℤ) : ℝ) / ((n : ℝ) + 1)
      if ENNReal.ofReal e < τ then
        ENNReal.ofReal (Real.exp (-(q * e))) else 0
    else 0
  let g : ℝ → ℝ≥0∞ := fun r =>
    if 0 < r then
      if ENNReal.ofReal r < τ then
        ENNReal.ofReal (Real.exp (-(q * r))) else 0
    else 0
  have hfmeas (n : ℕ) : Measurable (f n) := by
    change Measurable (fun r : ℝ =>
      if 0 < r then
        (let e := ((⌈r * ((n : ℝ) + 1)⌉ : ℤ) : ℝ) / ((n : ℝ) + 1)
         if ENNReal.ofReal e < τ then
           ENNReal.ofReal (Real.exp (-(q * e))) else 0)
      else 0)
    exact Measurable.ite
      (show MeasurableSet {r : ℝ | 0 < r} from measurableSet_Ioi)
      (avram_root29_05_killed_right_mesh_discount_measurable q τ n)
      measurable_const
  have hpoint (r : ℝ) : Tendsto (fun n => f n r) atTop (𝓝 (g r)) := by
    by_cases hr : 0 < r
    · simpa [f, g, hr] using
        (avram_root29_05_killed_right_mesh_discount_tendsto r q τ)
    · simp [f, g, hr]
  change (∫⁻ r, g r ∂μ) ≤
    liminf (fun n => ∫⁻ r, f n r ∂μ) atTop
  calc
    (∫⁻ r, g r ∂μ) =
        (∫⁻ r, liminf (fun n => f n r) atTop ∂μ) := by
      apply lintegral_congr
      intro r
      exact (hpoint r).liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ r, f n r ∂μ) atTop :=
      lintegral_liminf_le hfmeas
