-- Prove2me | solution 1 for AvramDividend.Classical.stieltjes_cumulative_of_monotone_continuous_zero_left
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T06:37:50.480847+00:00
-- url     : https://prove2.me/submissions/707306ac-c98e-46de-9030-8a8eaed705d9

import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Topology.Order.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory Set
open scoped NNReal ENNReal

/-- Continuous nondecreasing scale-like functions give finite positive Stieltjes cumulative masses. -/
theorem solution
    (f : ℝ → ℝ)
    (hmono : Monotone f)
    (hcont : Continuous f)
    (hleft : ∀ x : ℝ, x < 0 → f x = 0)
    (hpos : ∀ x : ℝ, 0 < x → 0 < f x) :
    ∃ β : Measure ℝ,
      (∀ x : ℝ, β (Iic x) = ENNReal.ofReal (f x)) ∧
      (∀ x : ℝ, β (Iic x) ≠ ⊤) ∧
      (∀ x : ℝ, 0 < x → 0 < β (Iic x)) := by
  let F : StieltjesFunction ℝ :=
    { toFun := f
      mono' := hmono
      right_continuous' := fun x => (hcont.continuousAt).continuousWithinAt }
  have hlim : Tendsto (F : ℝ → ℝ) atBot (nhds (0 : ℝ)) := by
    have heq : (F : ℝ → ℝ) =ᶠ[atBot] (fun _ => (0 : ℝ)) := by
      filter_upwards [eventually_lt_atBot (0 : ℝ)] with x hx
      exact hleft x hx
    exact tendsto_const_nhds.congr' heq.symm
  refine ⟨F.measure, ?_, ?_, ?_⟩
  · intro x
    simpa only [sub_zero] using (F.measure_Iic hlim x)
  · intro x
    rw [F.measure_Iic hlim x]
    exact ENNReal.ofReal_ne_top
  · intro x hx
    rw [F.measure_Iic hlim x]
    apply ENNReal.ofReal_pos.mpr
    change 0 < f x - (0 : ℝ)
    simpa only [sub_zero] using hpos x hx
