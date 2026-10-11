-- Prove2me | solution 1 for BlackScholesModel.callPayoff_integral_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T17:23:54.839929+00:00
-- url     : https://prove2.me/submissions/5251eb4e-8638-4218-b866-a3ce65412bf1

import Mathlib
import Definitions.Def_BlackScholesModel_Core

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff ENNReal
open BlackScholesModel

/-- Integrate (S_T-K)^+ as the asset digital minus the cash digital. -/
theorem solution (K r σ τ S : ℝ)
    (hK : 0 < K) (hσ : 0 < σ) (hτ : 0 < τ) (hS : 0 < S) :
    (∫ z, max (terminalPrice S r σ τ z - K) 0
      ∂(gaussianReal 0 1)) =
      (∫ z in {z | K < terminalPrice S r σ τ z},
        terminalPrice S r σ τ z ∂(gaussianReal 0 1)) -
      K * (gaussianReal 0 1).real
        {z | K < terminalPrice S r σ τ z} := by
  let μ : Measure ℝ := gaussianReal 0 1
  let A : Set ℝ := {z | K < terminalPrice S r σ τ z}
  let a : ℝ := σ * Real.sqrt τ
  let C : ℝ := S * Real.exp ((r - σ ^ 2 / 2) * τ)
  have hST (z : ℝ) :
      terminalPrice S r σ τ z = C * Real.exp (a * z) := by
    dsimp [C, a, terminalPrice]
    rw [Real.exp_add]
    ring
  have hbase : Integrable (fun z : ℝ => Real.exp (a * z)) μ :=
    ProbabilityTheory.integrable_exp_mul_gaussianReal a
  have hInt : Integrable (fun z : ℝ => terminalPrice S r σ τ z) μ := by
    have heq : (fun z : ℝ => terminalPrice S r σ τ z) =
        (fun z : ℝ => C * Real.exp (a * z)) := by
      funext z
      exact hST z
    rw [heq]
    exact hbase.const_mul C
  have hcont : Continuous (fun z : ℝ => terminalPrice S r σ τ z) := by
    unfold terminalPrice
    fun_prop
  have hmA : MeasurableSet A := by
    change MeasurableSet
      ((fun z : ℝ => terminalPrice S r σ τ z) ⁻¹' Set.Ioi K)
    exact measurableSet_Ioi.preimage hcont.measurable
  have hpiece :
      (fun z : ℝ => max (terminalPrice S r σ τ z - K) 0) =
      A.indicator (fun z : ℝ => terminalPrice S r σ τ z - K) := by
    funext z
    by_cases hz : K < terminalPrice S r σ τ z
    · have heq : max (terminalPrice S r σ τ z - K) 0 =
          terminalPrice S r σ τ z - K :=
        max_eq_left (sub_nonneg.mpr (le_of_lt hz))
      simp [A, hz, heq]
    · have heq : max (terminalPrice S r σ τ z - K) 0 = 0 :=
        max_eq_right (sub_nonpos.mpr (le_of_not_gt hz))
      simp [A, hz, heq]
  have hIntOn : IntegrableOn
      (fun z : ℝ => terminalPrice S r σ τ z) A μ :=
    hInt.integrableOn
  have hsub :
      (∫ z in A, terminalPrice S r σ τ z - K ∂μ) =
      (∫ z in A, terminalPrice S r σ τ z ∂μ) -
      (∫ z in A, (K : ℝ) ∂μ) := by
    exact MeasureTheory.integral_sub hIntOn (integrable_const K)
  have hconst : (∫ z in A, (K : ℝ) ∂μ) = K * μ.real A := by
    simp [MeasureTheory.integral_const, smul_eq_mul, mul_comm]
  change (∫ z, max (terminalPrice S r σ τ z - K) 0 ∂μ) =
    (∫ z in A, terminalPrice S r σ τ z ∂μ) - K * μ.real A
  rw [hpiece, MeasureTheory.integral_indicator hmA, hsub, hconst]