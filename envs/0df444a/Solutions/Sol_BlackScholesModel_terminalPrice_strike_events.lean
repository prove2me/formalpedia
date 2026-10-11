-- Prove2me | solution 1 for BlackScholesModel.terminalPrice_strike_events
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T16:54:34.215977+00:00
-- url     : https://prove2.me/submissions/6156a2aa-e324-47d5-a6b3-d3eb36fbc045

import Mathlib
import Definitions.Def_BlackScholesModel_Core

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff ENNReal
open BlackScholesModel

/-- The strike crossing events are Gaussian half-lines at minus d-minus. -/
theorem solution (S K r σ τ : ℝ)
    (hS : 0 < S) (hK : 0 < K) (hσ : 0 < σ) (hτ : 0 < τ) :
    {z : ℝ | K < terminalPrice S r σ τ z} =
      Set.Ioi (-dMinus S K r σ τ) ∧
    {z : ℝ | terminalPrice S r σ τ z < K} =
      Set.Iio (-dMinus S K r σ τ) := by
  have hD : 0 < σ * Real.sqrt τ :=
    mul_pos hσ (Real.sqrt_pos.2 hτ)
  have hD0 : σ * Real.sqrt τ ≠ 0 := ne_of_gt hD
  have hsqrt : Real.sqrt τ ^ 2 = τ :=
    Real.sq_sqrt (le_of_lt hτ)
  have harg :
      (r - σ ^ 2 / 2) * τ +
        (σ * Real.sqrt τ) * (-dMinus S K r σ τ) =
      -Real.log (S / K) := by
    unfold dMinus dPlus
    field_simp [hD0]
    nlinarith [hsqrt]
  have href :
      K = S * Real.exp ((r - σ ^ 2 / 2) * τ +
        (σ * Real.sqrt τ) * (-dMinus S K r σ τ)) := by
    rw [harg, Real.exp_neg, Real.exp_log (div_pos hS hK)]
    field_simp [ne_of_gt hS, ne_of_gt hK]
  constructor
  · ext z
    change K < terminalPrice S r σ τ z ↔ -dMinus S K r σ τ < z
    constructor
    · intro h
      rw [href, terminalPrice] at h
      have hexp := lt_of_mul_lt_mul_left h hS.le
      have hlog := Real.exp_lt_exp.mp hexp
      nlinarith [hlog, hD]
    · intro h
      calc
        K = S * Real.exp ((r - σ ^ 2 / 2) * τ +
          (σ * Real.sqrt τ) * (-dMinus S K r σ τ)) := href
        _ < S * Real.exp ((r - σ ^ 2 / 2) * τ +
          (σ * Real.sqrt τ) * z) := by
          exact mul_lt_mul_of_pos_left
            (Real.exp_lt_exp.mpr (by nlinarith [hD])) hS
        _ = terminalPrice S r σ τ z := rfl
  · ext z
    change terminalPrice S r σ τ z < K ↔ z < -dMinus S K r σ τ
    constructor
    · intro h
      rw [href, terminalPrice] at h
      have hexp := lt_of_mul_lt_mul_left h hS.le
      have hlog := Real.exp_lt_exp.mp hexp
      nlinarith [hlog, hD]
    · intro h
      calc
        terminalPrice S r σ τ z =
            S * Real.exp ((r - σ ^ 2 / 2) * τ +
              (σ * Real.sqrt τ) * z) := rfl
        _ < S * Real.exp ((r - σ ^ 2 / 2) * τ +
          (σ * Real.sqrt τ) * (-dMinus S K r σ τ)) := by
          exact mul_lt_mul_of_pos_left
            (Real.exp_lt_exp.mpr (by nlinarith [hD])) hS
        _ = K := href.symm