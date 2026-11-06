-- Prove2me | solution 1 for BianchiIX.scaled_core_projective_duration
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:36:57.422887+00:00
-- url     : https://prove2.me/submissions/c63c71f3-fff8-4e31-9b8c-1480d3090815

import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Theorems.Thm_BianchiIX_coreBootstrap_angle_bound
import Theorems.Thm_BianchiIX_coreBootstrap_clock_bounds
import Theorems.Thm_BianchiIX_hasDerivAt_coreAngle_scaled
import Theorems.Thm_BianchiIX_image_sub_le_clock_sub_of_deriv_le
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial

noncomputable section
open BianchiIX
open Set


theorem solution {β : ℝ → ProjectiveState} {a τ : ℝ → ℝ} {I : Set ℝ}
    {k s t : ℝ} (hk : 6 ≤ k) (hI : Convex ℝ I)
    (ha : ∀ u ∈ I, 0 ≤ a u)
    (hβ : ∀ u ∈ I, HasDerivAt β (a u • projectiveField (β u)) u)
    (hτ : ∀ u ∈ I, HasDerivAt τ (a u) u)
    (hr : ∀ u ∈ I, 99 / 100 * k ≤ coreRadius (β u 0) (β u 2) ∧
      coreRadius (β u 0) (β u 2) ≤ 101 / 100 * k)
    (hv : ∀ u ∈ I, 1 ≤ β u 2)
    (hu : ∀ u ∈ I, 0 ≤ β u 1 ∧ β u 1 ≤ (1 / 10000) / k)
    (hw : ∀ u ∈ I, 0 ≤ β u 3 ∧ β u 3 ≤ (1 / 10000) / k)
    (hs : s ∈ I) (ht : t ∈ I) (hst : s ≤ t) :
    τ t - τ s ≤ 4 * Real.log (4 * k) / k := by
  have hk0 : 0 < k := by linarith
  let z := fun u => coreAngle (β u 0) (β u 2)
  let q := fun u => a u * coreRadius (β u 0) (β u 2) *
    coreClockFactor (coreRadius (β u 0) (β u 2)) (β u 1) (β u 3)
  have hz (u : ℝ) (hh : u ∈ I) : HasDerivAt z (q u) u :=
    hasDerivAt_coreAngle_scaled (hβ u hh) (lt_of_lt_of_le zero_lt_one (hv u hh))
  have hspeed (u : ℝ) (hh : u ∈ I) : a u ≤ (2 / k) * q u := by
    have hd := (coreBootstrap_clock_bounds hk (hr u hh).1 (hu u hh) (hw u hh)).1
    have H := mul_le_mul (hr u hh).1 hd (by norm_num : (0 : ℝ) ≤ 999 / 1000)
      (by linarith [(hr u hh).1] : 0 ≤ coreRadius (β u 0) (β u 2))
    have hrd : k / 2 ≤ coreRadius (β u 0) (β u 2) *
        coreClockFactor (coreRadius (β u 0) (β u 2)) (β u 1) (β u 3) := by nlinarith
    have hq : a u * (k / 2) ≤ q u := by
      have H' := mul_le_mul_of_nonneg_left hrd (ha u hh)
      dsimp [q]
      nlinarith
    calc
      a u = (2 / k) * (a u * (k / 2)) := by field_simp
      _ ≤ (2 / k) * q u := mul_le_mul_of_nonneg_left hq (by positivity)
  have H := image_sub_le_clock_sub_of_deriv_le hI hτ hz hspeed hs ht hst
  have hzs := abs_le.mp (coreBootstrap_angle_bound hk (hr s hs).2 (hv s hs))
  have hzt := abs_le.mp (coreBootstrap_angle_bound hk (hr t ht).2 (hv t ht))
  calc
    τ t - τ s ≤ (2 / k) * (z t - z s) := H
    _ ≤ (2 / k) * (2 * Real.log (4 * k)) :=
      mul_le_mul_of_nonneg_left (by dsimp [z]; linarith) (by positivity)
    _ = 4 * Real.log (4 * k) / k := by ring
