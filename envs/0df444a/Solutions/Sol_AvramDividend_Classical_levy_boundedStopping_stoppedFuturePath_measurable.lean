-- Prove2me | solution 1 for AvramDividend.Classical.levy_boundedStopping_stoppedFuturePath_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T14:18:22.185174+00:00
-- url     : https://prove2.me/submissions/ff814613-a496-4632-aa99-722fa7467fd7

import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Algebra.Order.Group.MinMax
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_boundedStopping_stoppedFutureReward_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- A bounded Lévy stopping time yields a measurable entire shifted future-increment path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbound : ∀ ω, τ ω ≤ T) :
    Measurable (fun ω : Ω => fun t : ℝ≥0 =>
      X.X (τ ω + t) ω - X.X (τ ω) ω) := by
  have hA : ∀ s : ℝ≥0, MeasurableSet[𝓕 s]
      (Set.univ ∩ {ω : Ω | τ ω ≤ s}) := by
    intro s
    simpa only [Set.univ_inter, WithTop.coe_le_coe] using hstop s
  apply measurable_pi_iff.mpr
  intro t
  let v : Ω → ℝ := fun ω =>
    X.X (τ ω + t) ω - X.X (τ ω) ω
  let gpos : (ℝ≥0 → ℝ) → ℝ≥0∞ :=
    fun y => ENNReal.ofReal (y t)
  have hgpos : Continuous gpos :=
    ENNReal.continuous_ofReal.comp (continuous_apply t)
  have hgmpos : Measurable gpos :=
    ENNReal.measurable_ofReal.comp (measurable_pi_apply t)
  have hpos : Measurable (fun ω => ENNReal.ofReal (v ω)) := by
    simpa only [Set.indicator_univ, gpos, v] using
      (levy_boundedStopping_stoppedFutureReward_measurable
        X τ hstop T hbound Set.univ hA gpos hgpos hgmpos)
  let gneg : (ℝ≥0 → ℝ) → ℝ≥0∞ :=
    fun y => ENNReal.ofReal (-(y t))
  have hgneg : Continuous gneg :=
    ENNReal.continuous_ofReal.comp (continuous_apply t).neg
  have hgmneg : Measurable gneg :=
    ENNReal.measurable_ofReal.comp (measurable_pi_apply t).neg
  have hneg : Measurable (fun ω => ENNReal.ofReal (-(v ω))) := by
    simpa only [Set.indicator_univ, gneg, v] using
      (levy_boundedStopping_stoppedFutureReward_measurable
        X τ hstop T hbound Set.univ hA gneg hgneg hgmneg)
  have hreal : Measurable (fun ω =>
      (ENNReal.ofReal (v ω)).toReal -
        (ENNReal.ofReal (-(v ω))).toReal) :=
    (ENNReal.measurable_toReal.comp hpos).sub
      (ENNReal.measurable_toReal.comp hneg)
  have heq : (fun ω =>
      (ENNReal.ofReal (v ω)).toReal -
        (ENNReal.ofReal (-(v ω))).toReal) = v := by
    funext ω
    simp only [ENNReal.toReal_ofReal']
    exact max_zero_sub_max_neg_zero_eq_self (v ω)
  rw [heq] at hreal
  exact hreal
