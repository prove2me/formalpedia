-- Prove2me | solution 1 for AvramDividend.Classical.chat04_countable_two_sided_killed_scale_payoff_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T21:54:16.86595+00:00
-- url     : https://prove2.me/submissions/a14916d3-0b42-453b-8ba1-387918afb73a

import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_AvramDividend_Classical_chat04_countable_shifted_two_sided_survival_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable
open AvramDividend.Classical

/-- A q-scale reward killed at both barriers on a countable grid is Borel. -/
theorem solution
    (τ : ℕ → ℝ≥0) (T t : ℝ≥0) (a q : ℝ)
    (W : ℝ → ℝ) (hW : Measurable W) :
    Measurable (fun z : ℝ × (ℝ≥0 → ℝ) =>
      if ∀ j : ℕ, τ j ≤ T →
        0 ≤ z.1 + z.2 (τ j) ∧ z.1 + z.2 (τ j) ≤ a
      then ENNReal.ofReal (Real.exp (-(q * (t : ℝ))) * W (z.1 + z.2 t))
      else (0 : ℝ≥0∞)) := by
  have hSurvival : MeasurableSet
      {z : ℝ × (ℝ≥0 → ℝ) |
        ∀ j : ℕ, τ j ≤ T →
          0 ≤ z.1 + z.2 (τ j) ∧ z.1 + z.2 (τ j) ≤ a} :=
    chat04_countable_shifted_two_sided_survival_measurable τ T a
  have hEval : Measurable
      (fun z : ℝ × (ℝ≥0 → ℝ) => z.1 + z.2 t) :=
    measurable_fst.add ((measurable_pi_apply t).comp measurable_snd)
  have hPayoff : Measurable
      (fun z : ℝ × (ℝ≥0 → ℝ) =>
        ENNReal.ofReal (Real.exp (-(q * (t : ℝ))) * W (z.1 + z.2 t))) :=
    ENNReal.measurable_ofReal.comp
      (measurable_const.mul (hW.comp hEval))
  exact hPayoff.ite hSurvival measurable_const
