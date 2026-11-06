-- Prove2me | solution 1 for BianchiIX.coreRadius_flow_regular
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T02:02:08.997555+00:00
-- url     : https://prove2.me/submissions/69be3e76-6baf-4473-821a-c6a66a6aca71

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Theorems.Thm_BianchiIX_contDiffAt_fromProjectiveState
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Theorems.Thm_BianchiIX_normalizedMaxCurve_regular
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.Module
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
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
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology

private theorem BianchiIX.isOpen_normalizedFlowDomain (t₀ : ℝ) : IsOpen (normalizedFlowDomain t₀) := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  exact mem_interior_iff_mem_nhds.mp (normalizedMaxCurve_regular hz).1

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_coreRadiusEntry (n : WithTop ℕ∞) {Y : CoreAngleState} (hk : 1 < Y 0) :
    ContDiffAt ℝ n coreRadiusEntry Y := by
  have hs : Y 0 ^ 2 - 1 ≠ 0 := ne_of_gt (by nlinarith only [hk] : 0 < Y 0 ^ 2 - 1)
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [coreRadiusEntry] <;> fun_prop

end
end

theorem solution {Y : CoreAngleState} {t : ℝ}
    (hk : 1 < Y 0) (hD : 0 < projectiveStateDenom (coreRadiusEntry Y))
    (ht : t ∈ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry Y)) 0)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState (coreRadiusEntry Y)) 0 t 0) :
    (∀ᶠ q : CoreAngleState × ℝ in 𝓝 (Y, t),
      q.2 ∈ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry q.1)) 0 ∧
        0 < 1 + normalizedMaxCurve (fromProjectiveState (coreRadiusEntry q.1)) 0 q.2 0) ∧
      ContinuousAt (fun q : CoreAngleState × ℝ => projectiveOriginalFlow (coreRadiusEntry q.1) 0 q.2) (Y, t) := by
  have hc := ((contDiffAt_fromProjectiveState 1 (ne_of_gt hD)).comp Y
    (contDiffAt_coreRadiusEntry 1 hk)).continuousAt
  have hpair : ContinuousAt (fun q : CoreAngleState × ℝ =>
      (fromProjectiveState (coreRadiusEntry q.1), q.2)) (Y, t) := by
    convert! (hc.comp (continuousAt_fst : ContinuousAt (Prod.fst : CoreAngleState × ℝ → CoreAngleState)
      (Y, t))).prodMk continuousAt_snd using 1
  have hflow : ContinuousAt (fun q : CoreAngleState × ℝ =>
      normalizedMaxCurve (fromProjectiveState (coreRadiusEntry q.1)) 0 q.2) (Y, t) := by
    exact ContinuousAt.comp (g := fun q : NormalizedState × ℝ => normalizedMaxCurve q.1 0 q.2)
      (f := fun q : CoreAngleState × ℝ => (fromProjectiveState (coreRadiusEntry q.1), q.2))
      (normalizedMaxCurve_regular ht).2.continuousAt hpair
  have hclock : ContinuousAt (fun q : CoreAngleState × ℝ =>
      1 + normalizedMaxCurve (fromProjectiveState (coreRadiusEntry q.1)) 0 q.2 0) (Y, t) :=
    continuousAt_const.add (continuousAt_pi.mp hflow 0)
  refine ⟨(hpair.eventually ((isOpen_normalizedFlowDomain 0).mem_nhds ht)).and
    (hclock.eventually (isOpen_Ioi.mem_nhds hA)), ?_⟩
  exact ContinuousAt.comp (g := toProjectiveState)
    (f := fun q : CoreAngleState × ℝ => normalizedMaxCurve (fromProjectiveState (coreRadiusEntry q.1)) 0 q.2)
    (contDiffAt_toProjectiveState 1 (ne_of_gt hA)).continuousAt hflow
