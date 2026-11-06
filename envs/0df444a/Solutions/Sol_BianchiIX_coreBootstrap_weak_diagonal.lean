-- Prove2me | solution 1 for BianchiIX.coreBootstrap_weak_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T23:42:12.279323+00:00
-- url     : https://prove2.me/submissions/a565c859-d8a3-4c9c-807a-d8ed9c6552df

import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Theorems.Thm_BianchiIX_coreBootstrap_clock_bounds
import Theorems.Thm_BianchiIX_coreBootstrap_diagonal_factors
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin

noncomputable section
open BianchiIX


theorem solution {k r u w c : ℝ} (hk : 6 ≤ k)
    (hr : 99 / 100 * k ≤ r ∧ r ≤ 101 / 100 * k)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k) (hw : 0 ≤ w ∧ w ≤ (1 / 10000) / k)
    (hc : 0 ≤ c) :
    -2 * (1 + c) * (r ^ 2 - u ^ 2 + w ^ 2) / (r ^ 3 * coreClockFactor r u w ^ 2) -
      2 * u * w / (r * coreClockFactor r u w) ≤ -1 / k := by
  let d := coreClockFactor r u w
  have hr0 : 0 < r := by linarith [hr.1]
  have hk0 : 0 < k := by linarith
  have hd0 : 0 < d := by
    have H := (coreBootstrap_clock_bounds hk hr.1 hu hw).1
    change 999 / 1000 ≤ d at H
    linarith
  obtain ⟨_, hq, _⟩ := coreBootstrap_diagonal_factors hk hr.1 hu hw
  let q := (r ^ 2 - u ^ 2 + w ^ 2) / (r ^ 2 * d ^ 2)
  change 99 / 100 ≤ q at hq
  have hcq : 99 / 100 ≤ (1 + c) * q := by nlinarith
  have H := mul_le_mul_of_nonpos_left hcq
    (div_nonpos_of_nonpos_of_nonneg (by norm_num : (-2 : ℝ) ≤ 0) hr0.le)
  have hneg : -2 / r * (99 / 100) ≤ -1 / k := by
    calc
      -2 / r * (99 / 100) = (-198 / 100) / r := by ring
      _ ≤ -1 / k := (div_le_div_iff₀ hr0 hk0).mpr (by nlinarith [hr.2])
  have he := div_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hu.1) hw.1)
    (le_of_lt (mul_pos hr0 hd0))
  have hid : -2 * (1 + c) * (r ^ 2 - u ^ 2 + w ^ 2) / (r ^ 3 * d ^ 2) =
      (-2 / r) * ((1 + c) * q) := by dsimp [q]; ring
  change _ - 2 * u * w / (r * d) ≤ -1 / k
  rw [hid]
  linarith
