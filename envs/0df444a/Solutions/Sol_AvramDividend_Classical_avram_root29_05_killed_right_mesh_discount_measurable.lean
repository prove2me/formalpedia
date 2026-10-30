-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_05_killed_right_mesh_discount_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T10:28:18.611353+00:00
-- url     : https://prove2.me/submissions/35eacf6f-7dfd-48b5-b36a-9f01b54ac88e

import Mathlib
import Mathlib.MeasureTheory.Function.Floor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal Classical

/-- Measurability of the exact strictly killed, discounted first right-mesh
payment weight, required before applying Fatou to its Stieltjes integrals. -/
theorem solution (q : ℝ) (τ : ℝ≥0∞) (n : ℕ) :
    Measurable (fun r : ℝ =>
      let e := ((⌈r * ((n : ℝ) + 1)⌉ : ℤ) : ℝ) / ((n : ℝ) + 1)
      if ENNReal.ofReal e < τ then
        ENNReal.ofReal (Real.exp (-(q * e))) else 0) := by
  let e : ℝ → ℝ := fun r =>
    ((⌈r * ((n : ℝ) + 1)⌉ : ℤ) : ℝ) / ((n : ℝ) + 1)
  have hceil : Measurable (fun r : ℝ =>
      (⌈r * ((n : ℝ) + 1)⌉ : ℤ)) :=
    Int.measurable_ceil.comp (measurable_id.mul_const _)
  have hcast : Measurable (fun z : ℤ => (z : ℝ)) :=
    measurable_of_countable _
  have he : Measurable e :=
    (hcast.comp hceil).div_const _
  have hE : Measurable (fun r => ENNReal.ofReal (e r)) :=
    ENNReal.continuous_ofReal.measurable.comp he
  have hw : Measurable (fun r =>
      ENNReal.ofReal (Real.exp (-(q * e r)))) :=
    ENNReal.continuous_ofReal.measurable.comp
      (Real.continuous_exp.measurable.comp ((measurable_const.mul he).neg))
  change Measurable (fun r =>
    if ENNReal.ofReal (e r) < τ then
      ENNReal.ofReal (Real.exp (-(q * e r))) else 0)
  exact Measurable.ite (measurableSet_lt hE measurable_const) hw measurable_const
