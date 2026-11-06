-- Prove2me | solution 1 for BianchiIX.projectiveCoreAngle_fderiv_field
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T23:32:36.06483+00:00
-- url     : https://prove2.me/submissions/42e6b78d-f77c-47b0-9c8a-d3ad50988625

import Definitions.Def_BianchiIX_Dynamics_ProjectiveOriginalTime
import Definitions.Def_BianchiIX_Dynamics_CoreCoordinateDifferential
import Theorems.Thm_BianchiIX_hasDerivAt_coreAngle_scaled
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

private theorem BianchiIX.contDiffAt_projectiveCoreAngle (n : WithTop ℕ∞) {y : ProjectiveState}
    (hv : 0 < y 2) : ContDiffAt ℝ n projectiveCoreAngle y := by
  have hv0 := ne_of_gt hv
  unfold projectiveCoreAngle coreAngle
  fun_prop

theorem solution {y : ProjectiveState} (hv : 0 < y 2) :
    fderiv ℝ projectiveCoreAngle y (projectiveOriginalField y) = coreOriginalClockRate y := by
  let beta : ℝ → ProjectiveState := fun s => y + s • projectiveOriginalField y
  have hzero : beta 0 = y := by simp [beta]
  have hb : HasDerivAt beta (projectiveOriginalField (beta 0)) 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add
      ((hasDerivAt_id (0 : ℝ)).smul_const (projectiveOriginalField y)) using 1
    simp [hzero]
  have hc := ((contDiffAt_projectiveCoreAngle 1 hv).differentiableAt (by norm_num)).hasFDerivAt
  have H := (hzero.symm ▸ hc).comp_hasDerivAt 0 hb
  have H' := hasDerivAt_coreAngle_scaled hb (by simpa only [hzero] using hv)
  simpa only [hzero, coreOriginalClockRate, projectiveCoreAngle] using H.unique H'
