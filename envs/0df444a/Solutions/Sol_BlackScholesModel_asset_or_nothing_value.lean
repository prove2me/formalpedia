-- Prove2me | solution 1 for BlackScholesModel.asset_or_nothing_value
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T17:09:56.164791+00:00
-- url     : https://prove2.me/submissions/eb74c695-63a8-4545-ba24-0b22e0f1d0dd

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Theorems.Thm_BlackScholesModel_terminalPrice_strike_events
import Theorems.Thm_BlackScholesModel_gaussianReal_exponential_tilt_halfline

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff ENNReal
open BlackScholesModel

/-- Asset-or-nothing values from the two truncated exponentially tilted Gaussian moments. -/
theorem solution (K r σ T S t : ℝ)
    (hK : 0 < K) (hσ : 0 < σ) (hS : 0 < S) (ht : t < T) :
    Real.exp (-r * (T - t))
        * ∫ z in {z | K < terminalPrice S r σ (T - t) z},
          terminalPrice S r σ (T - t) z ∂(gaussianReal 0 1)
      = S * stdNormalCDF (dPlus S K r σ (T - t)) ∧
    Real.exp (-r * (T - t))
        * ∫ z in {z | terminalPrice S r σ (T - t) z < K},
          terminalPrice S r σ (T - t) z ∂(gaussianReal 0 1)
      = S * stdNormalCDF (-dPlus S K r σ (T - t)) := by
  let τ : ℝ := T - t
  let a : ℝ := σ * Real.sqrt τ
  let b : ℝ := -dMinus S K r σ τ
  have hτ : 0 < τ := sub_pos.mpr ht
  have hsqrt : Real.sqrt τ ^ 2 = τ := Real.sq_sqrt (le_of_lt hτ)
  have hST (z : ℝ) :
      terminalPrice S r σ τ z =
        (S * Real.exp (r * τ)) * Real.exp (a * z - a ^ 2 / 2) := by
    have harg :
        (r - σ ^ 2 / 2) * τ + a * z =
          r * τ + (a * z - a ^ 2 / 2) := by
      calc
        (r - σ ^ 2 / 2) * τ + a * z =
          (r - σ ^ 2 / 2) * Real.sqrt τ ^ 2 + a * z := by rw [hsqrt]
        _ = r * Real.sqrt τ ^ 2 + (a * z - a ^ 2 / 2) := by
          dsimp [a]
          ring
        _ = r * τ + (a * z - a ^ 2 / 2) := by rw [hsqrt]
    calc
      terminalPrice S r σ τ z =
        S * Real.exp ((r - σ ^ 2 / 2) * τ + a * z) := by rfl
      _ = S * Real.exp (r * τ + (a * z - a ^ 2 / 2)) := by rw [harg]
      _ = (S * Real.exp (r * τ)) * Real.exp (a * z - a ^ 2 / 2) := by
        rw [Real.exp_add]
        ring
  obtain ⟨heventUpper, heventLower⟩ :=
    terminalPrice_strike_events S K r σ τ hS hK hσ hτ
  obtain ⟨hmomUpper, hmomLower⟩ :=
    gaussianReal_exponential_tilt_halfline a b
  have hUpper :
      (∫ z in Set.Ioi b, terminalPrice S r σ τ z ∂(gaussianReal 0 1)) =
        (S * Real.exp (r * τ)) *
          (∫ z in Set.Ioi b, Real.exp (a * z - a ^ 2 / 2)
            ∂(gaussianReal 0 1)) := by
    simp_rw [hST]
    rw [MeasureTheory.integral_const_mul]
  have hLower :
      (∫ z in Set.Iio b, terminalPrice S r σ τ z ∂(gaussianReal 0 1)) =
        (S * Real.exp (r * τ)) *
          (∫ z in Set.Iio b, Real.exp (a * z - a ^ 2 / 2)
            ∂(gaussianReal 0 1)) := by
    simp_rw [hST]
    rw [MeasureTheory.integral_const_mul]
  have hplus : a - b = dPlus S K r σ τ := by
    dsimp [a, b, dMinus]
    ring
  have hminus : b - a = -dPlus S K r σ τ := by
    dsimp [a, b, dMinus]
    ring
  have hdisc : Real.exp (-r * τ) * Real.exp (r * τ) = 1 := by
    rw [← Real.exp_add]
    simp
  constructor
  · change Real.exp (-r * τ) *
        ∫ z in {z | K < terminalPrice S r σ τ z},
          terminalPrice S r σ τ z ∂(gaussianReal 0 1) =
        S * stdNormalCDF (dPlus S K r σ τ)
    rw [heventUpper, hUpper, hmomUpper, hplus]
    calc
      Real.exp (-r * τ) *
          ((S * Real.exp (r * τ)) * stdNormalCDF (dPlus S K r σ τ)) =
        (Real.exp (-r * τ) * Real.exp (r * τ)) *
          (S * stdNormalCDF (dPlus S K r σ τ)) := by ring
      _ = S * stdNormalCDF (dPlus S K r σ τ) := by rw [hdisc]; ring
  · change Real.exp (-r * τ) *
        ∫ z in {z | terminalPrice S r σ τ z < K},
          terminalPrice S r σ τ z ∂(gaussianReal 0 1) =
        S * stdNormalCDF (-dPlus S K r σ τ)
    rw [heventLower, hLower, hmomLower, hminus]
    calc
      Real.exp (-r * τ) *
          ((S * Real.exp (r * τ)) * stdNormalCDF (-dPlus S K r σ τ)) =
        (Real.exp (-r * τ) * Real.exp (r * τ)) *
          (S * stdNormalCDF (-dPlus S K r σ τ)) := by ring
      _ = S * stdNormalCDF (-dPlus S K r σ τ) := by rw [hdisc]; ring