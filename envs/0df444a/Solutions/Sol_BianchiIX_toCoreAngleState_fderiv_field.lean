-- Prove2me | solution 1 for BianchiIX.toCoreAngleState_fderiv_field
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T23:34:36.488227+00:00
-- url     : https://prove2.me/submissions/b18f2650-c178-4800-869f-f000f95fba6c

import Definitions.Def_BianchiIX_Dynamics_ProjectiveOriginalTime
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreCoordinateDifferential
import Theorems.Thm_BianchiIX_hasDerivAt_toCoreAngleState_scaled
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

noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_projectiveCoreRadius (n : WithTop ℕ∞) {y : ProjectiveState}
    (hv : 0 < y 2) : ContDiffAt ℝ n (fun z : ProjectiveState => coreRadius (z 0) (z 2)) y := by
  have he : coreEnergy (y 0) (y 2) ≠ 0 := by unfold coreEnergy; positivity
  have he' : (y 0 - 1) ^ 2 + y 2 ^ 2 ≠ 0 := he
  unfold coreRadius coreEnergy
  fun_prop

private theorem BianchiIX.contDiffAt_toCoreAngleState (n : WithTop ℕ∞) {y : ProjectiveState}
    (hv : 0 < y 2) : ContDiffAt ℝ n toCoreAngleState y := by
  have hr := contDiffAt_projectiveCoreRadius n hv
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [toCoreAngleState] <;> fun_prop

theorem solution {y : ProjectiveState} (hv : 0 < y 2)
    (hd : coreClockFactor (coreRadius (y 0) (y 2)) (y 1) (y 3) ≠ 0) :
    fderiv ℝ toCoreAngleState y (projectiveOriginalField y) =
      coreOriginalClockRate y • coreAngleField (projectiveCoreAngle y) (toCoreAngleState y) := by
  let beta : ℝ → ProjectiveState := fun s => y + s • projectiveOriginalField y
  have hzero : beta 0 = y := by simp [beta]
  have hb : HasDerivAt beta (projectiveOriginalField (beta 0)) 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add
      ((hasDerivAt_id (0 : ℝ)).smul_const (projectiveOriginalField y)) using 1
    simp [hzero]
  have hp := ((contDiffAt_toCoreAngleState 1 hv).differentiableAt (by norm_num)).hasFDerivAt
  have H := (hzero.symm ▸ hp).comp_hasDerivAt 0 hb
  have H' := hasDerivAt_toCoreAngleState_scaled hb
    (by simpa only [hzero] using hv) (by simpa only [hzero] using hd)
  simpa only [hzero, coreOriginalClockRate, projectiveCoreAngle] using H.unique H'
