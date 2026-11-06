-- Prove2me | solution 1 for BianchiIX.contDiffAt_coreLogRates_joint
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T02:28:12.036733+00:00
-- url     : https://prove2.me/submissions/437ce76c-6e20-462c-b083-792d08118e92

import Definitions.Def_BianchiIX_Dynamics_CoreLogRates
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

private theorem BianchiIX.contDiffAt_coreAuxiliary_joint (n : WithTop ℕ∞) (z : ℝ) {y : CoreAngleState}
    (hr : y 0 ≠ 0) :
    ContDiffAt ℝ n (fun p : ℝ × CoreAngleState => coreAuxiliary p.1 p.2) (z, y) := by
  have hz : Real.cosh z ≠ 0 := ne_of_gt (Real.cosh_pos z)
  have hv : y 0 / Real.cosh z ≠ 0 := div_ne_zero hr hz
  have hr2 : y 0 ^ 2 ≠ 0 := pow_ne_zero 2 hr
  have hr' : 2 * y 0 ≠ 0 := mul_ne_zero (by norm_num) hr
  have ht : ContDiffAt ℝ n (fun p : ℝ × CoreAngleState => Real.tanh p.1) (z, y) := by
    simp_rw [Real.tanh_eq_sinh_div_cosh]
    fun_prop
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [coreAuxiliary, coupling, coreClockFactor] <;> fun_prop

end
end

theorem solution (n : WithTop ℕ∞) (z : ℝ) {y : CoreAngleState}
    (hr : y 0 ≠ 0) (hd : coreAuxiliary z y 1 ≠ 0) :
    ContDiffAt ℝ n (fun p : ℝ × CoreAngleState => coreLogRates p.1 p.2) (z, y) := by
  have hq := contDiffAt_pi.mp (contDiffAt_coreAuxiliary_joint n z hr)
  have hrd : y 0 * coreAuxiliary z y 1 ≠ 0 := mul_ne_zero hr hd
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [coreLogRates] <;> fun_prop
