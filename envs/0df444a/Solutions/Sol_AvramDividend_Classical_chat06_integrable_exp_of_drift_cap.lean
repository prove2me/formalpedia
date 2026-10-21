-- Prove2me | solution 1 for AvramDividend.Classical.chat06_integrable_exp_of_drift_cap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T16:03:18.908537+00:00
-- url     : https://prove2.me/submissions/281b337b-3f2f-4e98-91d5-a022e01d82ca

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic.FunProp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

namespace AvramChat06

/-- For a probability measure, a measurable capital process bounded
above by its deterministic unit drift has every nonnegative-θ
exponential moment integrable, even with unbounded negative jumps.
This removes an independent hFint assumption from the exact
compound-Poisson Laplace count-conditioning lemma. -/
theorem integrable_exp_of_pointwise_upper_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (hZ : Measurable Z)
    (t θ : ℝ) (hθ : 0 ≤ θ)
    (hBound : ∀ ω, Z ω ≤ t) :
    Integrable (fun ω => Real.exp (θ * Z ω)) P := by
  have hm : Measurable (fun ω => Real.exp (θ * Z ω)) := by
    fun_prop
  apply Integrable.of_bound hm.aestronglyMeasurable
    (Real.exp (θ * t))
  filter_upwards [] with ω
  have hmul : θ * Z ω ≤ θ * t :=
    mul_le_mul_of_nonneg_left (hBound ω) hθ
  have hexp : Real.exp (θ * Z ω) ≤ Real.exp (θ * t) :=
    Real.exp_le_exp.mpr hmul
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hexp

end AvramChat06

open AvramChat06

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (hZ : Measurable Z)
    (t θ : ℝ) (hθ : 0 ≤ θ)
    (hBound : ∀ ω, Z ω ≤ t) :
    Integrable (fun ω => Real.exp (θ * Z ω)) P := by
  exact integrable_exp_of_pointwise_upper_bound Z hZ t θ hθ hBound
