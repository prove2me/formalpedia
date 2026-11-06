-- Prove2me | solution 1 for BianchiIX.coreTail_regular_of_valid
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T07:08:52.313815+00:00
-- url     : https://prove2.me/submissions/5f7be8da-a712-43b2-af63-31afab3240f0

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Theorems.Thm_BianchiIX_contDiffAt_fromProjectiveState
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Theorems.Thm_BianchiIX_eventually_forall_movingInterval
import Theorems.Thm_BianchiIX_exists_activeWall_first_downward_hit_two
import Theorems.Thm_BianchiIX_normalizedMaxCurve_regular
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
open Set Filter
open scoped Topology

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

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.coreTailValid_denom_pos {η : ℝ} {Y : CoreAngleState} (hvalid : coreTailValid η Y) :
    0 < projectiveStateDenom (coreTailEntry Y) := by
  have hzero := (hvalid.2.1 0 ⟨le_rfl, hvalid.1.1.1.le⟩).2
  rw [normalizedMaxCurve_initial] at hzero
  change 0 < 1 + (6 / projectiveStateDenom (coreTailEntry Y) - 1) at hzero
  by_contra! hn
  have H := div_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 6) hn
  linarith only [hzero, H]

end
end

/-- Every valid downward tail, including signed walls, has the same smooth canonical arrival map. -/
theorem solution {Y : CoreAngleState} {η : ℝ}
    (hR : 1 < Y 0) (H : coreTailValid η Y) :
    ContDiffAt ℝ 2 (coreTailTime η) Y ∧ ContDiffAt ℝ 2 (coreTailState η) Y ∧
      (∀ᶠ Z in 𝓝 Y, coreTailValid η Z) := by
  let c : CoreAngleState → NormalizedState := fun Z => fromProjectiveState (coreTailEntry Z)
  have hD := coreTailValid_denom_pos H
  have hcc : ContDiffAt ℝ 2 c Y :=
    (contDiffAt_fromProjectiveState 2 hD.ne').comp Y (contDiffAt_coreTailEntry 2 hR)
  obtain ⟨τ, hτ, hcτ, hcP, _, hnear⟩ := exists_activeWall_first_downward_hit_two H.1.1.1
    H.2.1 H.2.2.2.1 H.1.1.2.2
  have hsmall : ∀ᶠ x in 𝓝 (c Y), ∀ t ∈ Icc 0 (τ x),
      |toProjectiveState (normalizedMaxCurve x 0 t) 3| < 1 / 2 := by
    apply eventually_forall_movingInterval hcτ.continuousAt (by rw [hτ]; exact H.1.1.1)
    intro t ht
    rw [hτ] at ht
    have hreg := H.2.1 t ht
    have hf := (normalizedMaxCurve_regular hreg.1).2.continuousAt
    have hp : ContinuousAt (fun q : NormalizedState × ℝ =>
        toProjectiveState (normalizedMaxCurve q.1 0 q.2)) (c Y, t) :=
      ContinuousAt.comp (g := toProjectiveState) (f := fun q : NormalizedState × ℝ => normalizedMaxCurve q.1 0 q.2)
        (contDiffAt_toProjectiveState 1 hreg.2.ne').continuousAt hf
    exact (continuousAt_pi.mp hp 3).abs.eventually (isOpen_Iio.mem_nhds (H.2.2.2.2 t ht))
  have hnear' := hcc.continuousAt.eventually hnear
  have hsmall' := hcc.continuousAt.eventually hsmall
  have heq : coreTailTime η =ᶠ[𝓝 Y] (fun Z => τ (c Z)) := by
    filter_upwards [hnear'] with Z hZ
    exact hZ.1.csInf_eq
  have hcTime : ContDiffAt ℝ 2 (coreTailTime η) Y :=
    (hcτ.comp Y hcc).congr_of_eventuallyEq heq
  have hcOut : ContDiffAt ℝ 2 (coreTailState η) Y := by
    have hcomp := hcP.comp Y hcc
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [heq] with Z hZ
    dsimp only [coreTailState, projectiveOriginalFlow]
    rw [hZ]
    rfl
  refine ⟨hcTime, hcOut, ?_⟩
  filter_upwards [heq, hnear', hsmall'] with Z hZ hfirst hsmallZ
  dsimp only [coreTailValid]
  rw [hZ]
  exact ⟨hfirst.1, hfirst.2.1, hfirst.2.2.1, hfirst.2.2.2, hsmallZ⟩
