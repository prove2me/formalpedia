-- Prove2me | solution 1 for BianchiIX.coreLogRates_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T02:29:59.842378+00:00
-- url     : https://prove2.me/submissions/1456a604-ce1a-4f7d-996c-04742c597146

import Definitions.Def_BianchiIX_Dynamics_CoreLogRates
import Theorems.Thm_BianchiIX_hasDerivAt_coreLogRates
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

private theorem BianchiIX.contDiffAt_coreAuxiliary (n : WithTop ℕ∞) (z : ℝ) {y : CoreAngleState}
    (hr : y 0 ≠ 0) : ContDiffAt ℝ n (coreAuxiliary z) y := by
  have hv : y 0 / Real.cosh z ≠ 0 := div_ne_zero hr (ne_of_gt (Real.cosh_pos z))
  have hr2 : y 0 ^ 2 ≠ 0 := pow_ne_zero 2 hr
  have hr' : 2 * y 0 ≠ 0 := mul_ne_zero (by norm_num) hr
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [coreAuxiliary, coupling, coreClockFactor] <;> fun_prop

end
end

private theorem BianchiIX.contDiffAt_coreLogRates (n : WithTop ℕ∞) (z : ℝ) {y : CoreAngleState}
    (hr : y 0 ≠ 0) (hd : coreAuxiliary z y 1 ≠ 0) : ContDiffAt ℝ n (coreLogRates z) y := by
  have hq := contDiffAt_pi.mp (contDiffAt_coreAuxiliary n z hr)
  have hrd : y 0 * coreAuxiliary z y 1 ≠ 0 := mul_ne_zero hr hd
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [coreLogRates] <;> fun_prop

theorem solution (z : ℝ) {y : CoreAngleState}
    (hr : y 0 ≠ 0) (hd : coreAuxiliary z y 1 ≠ 0) (ξ : CoreAngleState) :
    fderiv ℝ (coreLogRates z) y ξ = (coreLogRateJacobian z y).mulVec ξ := by
  have hl : HasDerivAt (fun s : ℝ => y + s • ξ) ξ 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add ((hasDerivAt_id (0 : ℝ)).smul_const ξ) using 1
    simp
  have hzero : y + (0 : ℝ) • ξ = y := by simp
  have hf := ((contDiffAt_coreLogRates 1 z hr hd).differentiableAt (by norm_num)).hasFDerivAt
  have H := (hzero.symm ▸ hf).comp_hasDerivAt 0 hl
  simpa only [hzero] using H.unique (hasDerivAt_coreLogRates hl
    (by simpa only [hzero] using hr) (by simpa only [hzero] using hd))
