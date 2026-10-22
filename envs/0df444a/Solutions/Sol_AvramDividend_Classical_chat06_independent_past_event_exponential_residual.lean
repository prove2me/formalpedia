-- Prove2me | solution 1 for AvramDividend.Classical.chat06_independent_past_event_exponential_residual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T06:47:53.341081+00:00
-- url     : https://prove2.me/submissions/88643212-c3f3-47f4-8c13-da7b05eb7b4c

import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace AvramChat06

/-- Full measurable-past event conditioning for an independent
unit exponential wait, with random nonnegative age determined by
the past. This is the stochastic renewal factorisation needed
to extend individual waiting-time memorylessness to the entire
natural filtration. -/
theorem independent_past_event_exponential_residual
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (Z : Ω → E) (τ : Ω → ℝ) (age : E → ℝ)
    (hZ : Measurable Z) (hτ : Measurable τ)
    (hAgeMeas : Measurable age) (hInd : IndepFun Z τ P)
    (D : Set E) (hD : MeasurableSet D)
    (hNonneg : ∀ᵐ z ∂(P.map Z), 0 ≤ age z)
    (hTail : ∀ u : ℝ, 0 ≤ u →
      P {ω | u < τ ω} = ENNReal.ofReal (Real.exp (-u)))
    (t : ℝ) (ht : 0 ≤ t) :
    P {ω | Z ω ∈ D ∧ age (Z ω) + t < τ ω} =
      P {ω | Z ω ∈ D ∧ age (Z ω) < τ ω} *
        ENNReal.ofReal (Real.exp (-t)) := by
  classical
  let μ : Measure E := P.map Z
  let ν : Measure ℝ := P.map τ
  let T (u : ℝ) : Set (E × ℝ) :=
    {p | p.1 ∈ D ∧ age p.1 + u < p.2}
  have hm (u : ℝ) : MeasurableSet (T u) := by
    have hmAge : Measurable (fun p : E × ℝ => age p.1) :=
      hAgeMeas.comp measurable_fst
    have hmDiff : Measurable (fun p : E × ℝ =>
        p.2 - age p.1) :=
      measurable_snd.sub hmAge
    have hmLt : MeasurableSet {p : E × ℝ |
        u < p.2 - age p.1} :=
      hmDiff measurableSet_Ioi
    have heq : {p : E × ℝ | age p.1 + u < p.2} =
        {p : E × ℝ | u < p.2 - age p.1} := by
      ext p
      change (age p.1 + u < p.2) ↔
        (u < p.2 - age p.1)
      constructor <;> intro h <;> linarith
    change MeasurableSet
      ({p : E × ℝ | p.1 ∈ D} ∩
       {p : E × ℝ | age p.1 + u < p.2})
    exact (measurable_fst hD).inter (heq ▸ hmLt)
  have hJoint :
      P.map (fun ω => (Z ω, τ ω)) = μ.prod ν :=
    hInd.map_prod_eq_prod_map_map
      hZ.aemeasurable hτ.aemeasurable
  have hSlice (u : ℝ) (z : E) :
      ν (Prod.mk z ⁻¹' T u) =
        if z ∈ D then ν (Ioi (age z + u)) else 0 := by
    by_cases hz : z ∈ D
    · have hSet : Prod.mk z ⁻¹' T u = Ioi (age z + u) := by
        ext r
        simp [T, hz]
      rw [hSet, if_pos hz]
    · have hEmpty : Prod.mk z ⁻¹' T u = ∅ := by
        ext r
        simp [T, hz]
      rw [hEmpty, measure_empty, if_neg hz]
  have hIntegral (u : ℝ) :
      P {ω | Z ω ∈ D ∧ age (Z ω) + u < τ ω} =
        ∫⁻ z, (if z ∈ D then ν (Ioi (age z + u)) else 0) ∂μ := by
    calc
      P {ω | Z ω ∈ D ∧ age (Z ω) + u < τ ω} =
          (P.map (fun ω => (Z ω, τ ω))) (T u) := by
        rw [Measure.map_apply (hZ.prodMk hτ) (hm u)]
        rfl
      _ = (μ.prod ν) (T u) := by rw [hJoint]
      _ = ∫⁻ z, (if z ∈ D then
            ν (Ioi (age z + u)) else 0) ∂μ := by
        rw [Measure.prod_apply (hm u)]
        congr 1
        funext z
        exact hSlice u z
  have hTailMap (u : ℝ) (hu : 0 ≤ u) :
      ν (Ioi u) = ENNReal.ofReal (Real.exp (-u)) := by
    rw [Measure.map_apply hτ measurableSet_Ioi]
    exact hTail u hu
  have hAE : (fun z => if z ∈ D then
      ν (Ioi (age z + t)) else 0) =ᵐ[μ]
      (fun z => (if z ∈ D then ν (Ioi (age z)) else 0) *
        ENNReal.ofReal (Real.exp (-t))) := by
    filter_upwards [hNonneg] with z hz
    by_cases hdz : z ∈ D
    · simp only [hdz, if_pos]
      rw [hTailMap (age z + t) (add_nonneg hz ht),
        hTailMap (age z) hz]
      rw [show -(age z + t) = -age z + -t by ring,
        Real.exp_add,
        ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _))]
    · simp [hdz]
  calc
    P {ω | Z ω ∈ D ∧ age (Z ω) + t < τ ω} =
        ∫⁻ z, (if z ∈ D then
          ν (Ioi (age z + t)) else 0) ∂μ := hIntegral t
    _ = ∫⁻ z, ((if z ∈ D then
          ν (Ioi (age z)) else 0) *
          ENNReal.ofReal (Real.exp (-t))) ∂μ :=
      lintegral_congr_ae hAE
    _ = (∫⁻ z, (if z ∈ D then
          ν (Ioi (age z)) else 0) ∂μ) *
          ENNReal.ofReal (Real.exp (-t)) := by
      rw [lintegral_mul_const' (ENNReal.ofReal (Real.exp (-t)))
        (fun z => if z ∈ D then ν (Ioi (age z)) else 0)
        (by simp)]
    _ = P {ω | Z ω ∈ D ∧ age (Z ω) < τ ω} *
          ENNReal.ofReal (Real.exp (-t)) := by
      have h0 := hIntegral 0
      simp only [add_zero] at h0
      rw [h0]

end AvramChat06

open AvramChat06

theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (Z : Ω → E) (τ : Ω → ℝ) (age : E → ℝ)
    (hZ : Measurable Z) (hτ : Measurable τ)
    (hAgeMeas : Measurable age) (hInd : IndepFun Z τ P)
    (D : Set E) (hD : MeasurableSet D)
    (hNonneg : ∀ᵐ z ∂(P.map Z), 0 ≤ age z)
    (hTail : ∀ u : ℝ, 0 ≤ u →
      P {ω | u < τ ω} = ENNReal.ofReal (Real.exp (-u)))
    (t : ℝ) (ht : 0 ≤ t) :
    P {ω | Z ω ∈ D ∧ age (Z ω) + t < τ ω} =
      P {ω | Z ω ∈ D ∧ age (Z ω) < τ ω} *
        ENNReal.ofReal (Real.exp (-t)) := by
  exact independent_past_event_exponential_residual
    Z τ age hZ hτ hAgeMeas hInd D hD hNonneg hTail t ht
