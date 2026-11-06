-- Prove2me | solution 1 for BianchiIX.contDiffAt_coreTailMultiplier_two
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T06:10:01.876468+00:00
-- url     : https://prove2.me/submissions/355cf85c-b7ac-4e54-afd7-599012a18e61

import Definitions.Def_BianchiIX_Dynamics_CoreTailMultipliers
import Theorems.Thm_BianchiIX_contDiffAt_fromProjectiveState
import Theorems.Thm_BianchiIX_contDiffAt_normalizedProjectiveWallMultiplier_two
import Theorems.Thm_BianchiIX_fromProjectiveState_clock_pos
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open BianchiIX
open Set

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_coreTailEntry (n : WithTop ℕ∞) {Y : CoreAngleState} (hk : 1 < Y 0) :
    ContDiffAt ℝ n coreTailEntry Y := by
  have hs : Y 0 ^ 2 - 1 ≠ 0 := ne_of_gt (by nlinarith only [hk] : 0 < Y 0 ^ 2 - 1)
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [coreTailEntry] <;> fun_prop

end
end

private theorem BianchiIX.coreTailValid_denom_pos {η : ℝ} {Y : CoreAngleState} (hvalid : coreTailValid η Y) :
    0 < projectiveStateDenom (coreTailEntry Y) := by
  have hzero := (hvalid.2.1 0 ⟨le_rfl, hvalid.1.1.1.le⟩).2
  rw [normalizedMaxCurve_initial] at hzero
  change 0 < 1 + (6 / projectiveStateDenom (coreTailEntry Y) - 1) at hzero
  by_contra! hn
  have H := div_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 6) hn
  linarith only [hzero, H]

theorem solution {η : ℝ} {Y : CoreAngleState}
    (hk : 1 < Y 0) (hvalid : coreTailValid η Y) (hτ : ContDiffAt ℝ 2 (coreTailTime η) Y)
    (i : Fin 2) :
    ContDiffAt ℝ 2 (fun Z => coreTailMultiplier η Z i) Y ∧
      ContDiffAt ℝ 2 (fun Z => Real.log (coreTailMultiplier η Z i)) Y := by
  have hD := coreTailValid_denom_pos hvalid
  have hc : ContDiffAt ℝ 2 (fun Z => fromProjectiveState (coreTailEntry Z)) Y :=
    (contDiffAt_fromProjectiveState 2 hD.ne').comp Y (contDiffAt_coreTailEntry 2 hk)
  exact contDiffAt_normalizedProjectiveWallMultiplier_two hc hτ hvalid.1.1.1.le
    (fun _ ht => (hvalid.2.1 _ ht).1) (fromProjectiveState_clock_pos hD)
    (hvalid.2.1 _ ⟨hvalid.1.1.1.le, le_rfl⟩).2 (if i = 0 then 0 else 2)
