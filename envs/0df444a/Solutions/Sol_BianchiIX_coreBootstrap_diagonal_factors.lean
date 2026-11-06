-- Prove2me | solution 1 for BianchiIX.coreBootstrap_diagonal_factors
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T23:33:45.123042+00:00
-- url     : https://prove2.me/submissions/55133a23-7026-472a-88c3-2602ae8578a7

import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Theorems.Thm_BianchiIX_coreBootstrap_clock_bounds
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

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreBootstrap_wall_bound {k u : ℝ} (hk : 6 ≤ k) (hu : u ≤ (1 / 10000) / k) :
    u ≤ 1 / 60000 := by
  have hk0 : 0 < k := by linarith
  exact hu.trans ((div_le_iff₀ hk0).mpr (by linarith))

end
end

theorem solution {k r u w : ℝ} (hk : 6 ≤ k)
    (hr : 99 / 100 * k ≤ r)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k) (hw : 0 ≤ w ∧ w ≤ (1 / 10000) / k) :
    let d := coreClockFactor r u w
    99 / 100 ≤ (r ^ 2 + u ^ 2 - w ^ 2) / (r ^ 2 * d ^ 2) ∧
    99 / 100 ≤ (r ^ 2 - u ^ 2 + w ^ 2) / (r ^ 2 * d ^ 2) ∧
    u ^ 2 / (r * d) ≤ 1 / 100 := by
  let d := coreClockFactor r u w
  have hr5 : 5 ≤ r := by linarith
  have hr0 : 0 < r := by linarith
  have hr2 : 25 ≤ r ^ 2 := by nlinarith [sq_nonneg (r - 5)]
  obtain ⟨hdlo, hdhi⟩ := coreBootstrap_clock_bounds hk hr hu hw
  change 999 / 1000 ≤ d at hdlo
  change d ≤ 1 at hdhi
  have hd0 : 0 < d := by linarith
  have hu' := coreBootstrap_wall_bound hk hu.2
  have hw' := coreBootstrap_wall_bound hk hw.2
  have hu2 : u ^ 2 ≤ (1 / 60000 : ℝ) ^ 2 := (sq_le_sq₀ hu.1 (by norm_num)).mpr hu'
  have hw2 : w ^ 2 ≤ (1 / 60000 : ℝ) ^ 2 := (sq_le_sq₀ hw.1 (by norm_num)).mpr hw'
  have hd2 : d ^ 2 ≤ 1 := by nlinarith
  have hden : r ^ 2 * d ^ 2 ≤ r ^ 2 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hd2 (sq_nonneg r)
  have hden0 : 0 < r ^ 2 * d ^ 2 := by positivity
  have hrd : 1 ≤ r * d := by nlinarith
  refine ⟨(le_div_iff₀ hden0).mpr ?_, (le_div_iff₀ hden0).mpr ?_,
    (div_le_iff₀ (mul_pos hr0 hd0)).mpr ?_⟩
  · nlinarith only [hden, hw2, hr2, sq_nonneg u]
  · nlinarith only [hden, hu2, hr2, sq_nonneg w]
  · nlinarith only [hu2, hrd]
