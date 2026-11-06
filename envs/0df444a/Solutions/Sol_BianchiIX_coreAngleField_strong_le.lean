-- Prove2me | solution 1 for BianchiIX.coreAngleField_strong_le
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:03:39.759717+00:00
-- url     : https://prove2.me/submissions/206f1388-18aa-4222-ba3a-c2ee435ed684

import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Theorems.Thm_BianchiIX_coreBootstrap_clock_bounds
import Theorems.Thm_BianchiIX_coreBootstrap_strong_numerator
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
import Mathlib.Analysis.Calculus.FDeriv.Partial

noncomputable section
open BianchiIX
open Set

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreBootstrap_strong_rate {k r u v w c : ℝ} (hk : 6 ≤ k)
    (hr : 99 / 100 * k ≤ r) (hv : v ≤ r) (hc : -1 ≤ c)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k) (hw : 0 ≤ w ∧ w ≤ (1 / 10000) / k) :
    (-r / 2 - c + (v / r) * w + (u ^ 2 - w ^ 2) / (2 * r)) / coreClockFactor r u w ≤ -k / 4 := by
  have ha := coreBootstrap_strong_numerator hk hr hv hc hu hw
  obtain ⟨hdlo, hdhi⟩ := coreBootstrap_clock_bounds hk hr hu hw
  apply (div_le_iff₀ (show 0 < coreClockFactor r u w by linarith)).mpr
  nlinarith

end
end

theorem solution {k z : ℝ} {y : CoreAngleState} (hk : 6 ≤ k)
    (hr : 99 / 100 * k ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ (1 / 10000) / k)
    (hw : 0 ≤ y 2 / (y 0 / Real.cosh z) ∧ y 2 / (y 0 / Real.cosh z) ≤ (1 / 10000) / k) :
    coreAngleField z y 1 ≤ (-k / 4) * y 1 := by
  have hr0 : 0 < y 0 := by linarith
  have hv : y 0 / Real.cosh z ≤ y 0 :=
    (div_le_iff₀ (Real.cosh_pos z)).mpr (le_mul_of_one_le_right hr0.le (Real.one_le_cosh z))
  have ha := coreBootstrap_strong_rate hk hr hv
    (show -1 ≤ -Real.tanh z by linarith [Real.tanh_lt_one z]) hu hw
  have hd := ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 999 / 1000)
    (coreBootstrap_clock_bounds hk hr hu hw).1)
  have hrne := ne_of_gt hr0
  have H := mul_le_mul_of_nonneg_left ha hu.1
  convert! H using 1
  · dsimp [coreAngleField]
    field_simp
    ring
  · ring
