-- Prove2me | solution 1 for AvramDividend.Classical.levy_finiteStopping_stoppedFuturePath_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T14:32:13.703986+00:00
-- url     : https://prove2.me/submissions/ae9b81a5-f196-4b61-8bf4-e9ac0f870d83

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Topology.Constructions
import Mathlib.Order.WithBot
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_boundedStopping_stoppedFuturePath_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Truncation at integer horizons yields a measurable future-increment path at every finite stopping time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0))) :
    Measurable (fun ω : Ω => fun t : ℝ≥0 =>
      X.X (τ ω + t) ω - X.X (τ ω) ω) := by
  apply measurable_pi_iff.mpr
  intro t
  have hmeas (n : ℕ) : Measurable (fun ω : Ω =>
      X.X (min (τ ω) (n : ℝ≥0) + t) ω -
        X.X (min (τ ω) (n : ℝ≥0)) ω) := by
    let τn : Ω → ℝ≥0 := fun ω => min (τ ω) (n : ℝ≥0)
    have hstopn : IsStoppingTime 𝓕
        (fun ω => (τn ω : WithTop ℝ≥0)) := by
      simpa only [τn, WithTop.coe_min] using
        (IsStoppingTime.min_const hstop (n : ℝ≥0))
    have hsmall : ∀ ω, τn ω ≤ (n : ℝ≥0) :=
      fun ω => min_le_right _ _
    have hpath := levy_boundedStopping_stoppedFuturePath_measurable
      X τn hstopn (n : ℝ≥0) hsmall
    exact (measurable_pi_apply t).comp hpath
  apply measurable_of_tendsto_metrizable hmeas
  rw [tendsto_pi_nhds]
  intro ω
  obtain ⟨N, hN⟩ := exists_nat_ge (τ ω)
  refine (tendsto_congr' ?_).2 tendsto_const_nhds
  filter_upwards [eventually_ge_atTop N] with n hn
  have hle : τ ω ≤ (n : ℝ≥0) :=
    hN.trans (by exact_mod_cast hn)
  simp only [min_eq_left hle]
