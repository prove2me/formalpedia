-- Prove2me | solution 1 for BianchiIX.coreRadiusEntry_angle_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T01:55:47.724698+00:00
-- url     : https://prove2.me/submissions/3533797f-f190-401b-b7f6-fb7bd53871d4

import Definitions.Def_BianchiIX_Dynamics_CoreCoordinateDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Theorems.Thm_BianchiIX_coreCoordinate_fderiv
import Theorems.Thm_BianchiIX_coreRadiusEntry_fderiv
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.Module
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.ContDiff.Operations
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
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_projectiveCoreAngle (n : WithTop ℕ∞) {y : ProjectiveState}
    (hv : 0 < y 2) : ContDiffAt ℝ n projectiveCoreAngle y := by
  have hv0 := ne_of_gt hv
  unfold projectiveCoreAngle coreAngle
  fun_prop

end
end

private theorem BianchiIX.coreRadius_coreRadiusEntry {Y : CoreAngleState} (hk : 1 < Y 0) :
    coreRadius (coreRadiusEntry Y 0) (coreRadiusEntry Y 2) = Y 0 := by
  have hk0 : 0 < Y 0 := lt_trans zero_lt_one hk
  have hsq := Real.sq_sqrt (by nlinarith only [hk] : 0 ≤ Y 0 ^ 2 - 1)
  have he : coreEnergy (coreRadiusEntry Y 0) (coreRadiusEntry Y 2) = Y 0 ^ 2 := by
    dsimp [coreRadiusEntry, coreEnergy]
    nlinarith only [hsq]
  rw [coreRadius, he, Real.sqrt_sq hk0.le]

private theorem BianchiIX.contDiffAt_coreRadiusEntry (n : WithTop ℕ∞) {Y : CoreAngleState} (hk : 1 < Y 0) :
    ContDiffAt ℝ n coreRadiusEntry Y := by
  have hs : Y 0 ^ 2 - 1 ≠ 0 := ne_of_gt (by nlinarith only [hk] : 0 < Y 0 ^ 2 - 1)
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [coreRadiusEntry] <;> fun_prop

private theorem BianchiIX.coreRadiusEntry_angle_differential {Y : CoreAngleState} (hk : 1 < Y 0) (v : CoreAngleState) :
    fderiv ℝ projectiveCoreAngle (coreRadiusEntry Y) (fderiv ℝ coreRadiusEntry Y v) =
      -v 0 / Real.sqrt (Y 0 ^ 2 - 1) := by
  have hk0 : Y 0 ≠ 0 := ne_of_gt (lt_trans zero_lt_one hk)
  rw [(coreCoordinate_fderiv (show 0 < coreRadiusEntry Y 2 by change (0 : ℝ) < 1; norm_num) _).2,
    coreRadius_coreRadiusEntry hk, coreRadiusEntry_fderiv hk]
  dsimp [coreRadiusEntry]
  field_simp
  ring

theorem solution {Y : CoreAngleState} (hk : 1 < Y 0) (v : CoreAngleState) :
    fderiv ℝ (fun Z => projectiveCoreAngle (coreRadiusEntry Z)) Y v =
      -v 0 / Real.sqrt (Y 0 ^ 2 - 1) := by
  have hentry := ((contDiffAt_coreRadiusEntry 1 hk).differentiableAt (by norm_num)).hasFDerivAt
  have hangle := ((contDiffAt_projectiveCoreAngle 1
    (show 0 < coreRadiusEntry Y 2 by change (0 : ℝ) < 1; norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt
  have H : HasFDerivAt (fun Z => projectiveCoreAngle (coreRadiusEntry Z))
      ((fderiv ℝ projectiveCoreAngle (coreRadiusEntry Y)).comp (fderiv ℝ coreRadiusEntry Y)) Y := by
    convert! hangle.comp Y hentry using 1
  rw [H.fderiv, ContinuousLinearMap.comp_apply]
  exact coreRadiusEntry_angle_differential hk v
