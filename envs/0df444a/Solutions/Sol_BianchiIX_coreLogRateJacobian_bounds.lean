-- Prove2me | solution 1 for BianchiIX.coreLogRateJacobian_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T02:32:42.550568+00:00
-- url     : https://prove2.me/submissions/02c14878-849b-4058-8620-a1856d1a111a

import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreLogRates
import Theorems.Thm_BianchiIX_coreBootstrap_coefficient_scales
import Theorems.Thm_BianchiIX_coreLogRateJacobian_radius_bounds
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


/-- The six estimates in (B.39), retaining the small wall factor in both small columns. -/
theorem solution {k z : ℝ} {y : CoreAngleState}
    (hk : 6 ≤ k) (hr : 99 / 100 * k ≤ y 0 ∧ y 0 ≤ 101 / 100 * k)
    (hv : 1 ≤ y 0 / Real.cosh z)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ (1 / 10000) / k)
    (hw : 0 ≤ y 2 / (y 0 / Real.cosh z) ∧ y 2 / (y 0 / Real.cosh z) ≤ (1 / 10000) / k) :
    let J := coreLogRateJacobian z y
    |J 0 0| ≤ 2 ∧ |J 0 1| ≤ 4 * (1 / 10000) / k ^ 2 ∧ |J 0 2| ≤ 4 / k ∧
      |J 1 0| ≤ 8 / k ^ 2 ∧ |J 1 1| ≤ 8 ∧ |J 1 2| ≤ 8 * (1 / 10000) / k ^ 2 := by
  intro J
  let r := y 0
  let m := (1 / 10000) / k
  have hk0 : 0 < k := by linarith only [hk]
  obtain ⟨hr5, hm0, _, _, _, hkr, hk2r2, _⟩ := coreBootstrap_coefficient_scales hk hr
  have hr0 : 0 < r := by dsimp [r]; linarith only [hr5]
  have hkr' : k / r ≤ 10 / 9 := (div_le_iff₀ hr0).mpr (by dsimp [r]; linarith only [hr.1, hk])
  have hsmall : (7 / 2) * m / r ≤ 4 * (1 / 10000) / k ^ 2 := by
    calc
      _ = ((7 / 2) * (k / r)) * (m / k) := by field_simp
      _ ≤ ((7 / 2) * (10 / 9)) * (m / k) := by gcongr
      _ ≤ 4 * (m / k) := mul_le_mul_of_nonneg_right (by norm_num) (by dsimp [m]; positivity)
      _ = _ := by dsimp [m]; ring
  obtain ⟨h00, h01, h02, h10, h11, h12⟩ := coreLogRateJacobian_radius_bounds hk hr hv hu hw
  refine ⟨h00, h01.trans hsmall, ?_, ?_, by linarith only [h11], ?_⟩
  · apply h02.trans
    calc
      2 / r = (2 * (k / r)) / k := by field_simp
      _ ≤ (2 * (3 / 2)) / k := by gcongr
      _ ≤ 4 / k := div_le_div_of_nonneg_right (by norm_num) hk0.le
  · apply h10.trans
    calc
      5 / r ^ 2 = (5 * (k ^ 2 / r ^ 2)) / k ^ 2 := by field_simp
      _ ≤ (5 * (3 / 2)) / k ^ 2 := by gcongr
      _ ≤ 8 / k ^ 2 := div_le_div_of_nonneg_right (by norm_num) (sq_nonneg k)
  · exact (h12.trans hsmall).trans (div_le_div_of_nonneg_right (by norm_num) (sq_nonneg k))
