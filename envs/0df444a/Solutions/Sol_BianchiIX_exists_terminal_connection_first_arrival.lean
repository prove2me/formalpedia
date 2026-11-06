-- Prove2me | solution 1 for BianchiIX.exists_terminal_connection_first_arrival
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T18:12:23.12576+00:00
-- url     : https://prove2.me/submissions/6a252ec8-3712-4090-bd64-e25335dd6226

import Definitions.Def_BianchiIX_Dynamics_AxisMaps
import Definitions.Def_BianchiIX_TerminalConnectionData
import Theorems.Thm_BianchiIX_coreTail_regular_of_valid
import Theorems.Thm_BianchiIX_entranceReturn_existing_orbit
import Theorems.Thm_BianchiIX_entranceReturn_regular
import Theorems.Thm_BianchiIX_exists_terminal_cycle_entrance_inputs
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Module
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open BianchiIX
open Set

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisCycle_constraint (x : NormalizedState) : stateConstraint (axisCycle x) = stateConstraint x := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  dsimp [stateConstraint, constraint, shearSq, curvature, axisCycle]
  ring_nf
  norm_num [hs]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiff_projectiveCycleDenom (n : WithTop ℕ∞) : ContDiff ℝ n projectiveCycleDenom := by
  unfold projectiveCycleDenom axisCycleDenom curvature
  fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_projectiveCycle (n : WithTop ℕ∞) {y : ProjectiveState}
    (hH : projectiveCycleDenom y ≠ 0) : ContDiffAt ℝ n projectiveCycle y := by
  have hD := (contDiff_projectiveCycleDenom n).contDiffAt (x := y)
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · change ContDiffAt ℝ n (fun z : ProjectiveState => 1 - 4 * (z 0 + 1) / projectiveCycleDenom z) y
    fun_prop (disch := assumption)
  all_goals
    change ContDiffAt ℝ n (fun z : ProjectiveState => 4 * z _ / projectiveCycleDenom z) y
    fun_prop (disch := assumption)

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

private theorem BianchiIX.terminalConnection_regular_of_entrance {h : ℝ} {Y : ExitTailState}
    (hR : 1 < Y 0) (HV : coreTailValid h Y) (hH : projectiveCycleDenom (coreTailState h Y) ≠ 0) :
    let z := projectiveCycle (coreTailState h Y)
    7 / 4 ≤ coreRadius (z 0) (z 2) → 1 ≤ z 0 →
    (0 ≤ z 1 ∧ z 1 ≤ 1 / 10000) → (0 < z 2 ∧ z 2 < 1) →
    (0 ≤ z 3 ∧ z 3 ≤ 1 / 10000) →
    ContDiffAt ℝ 2 (terminalConnectionTime h) Y ∧ ContDiffAt ℝ 2 (terminalConnectionState h) Y := by
  intro z hk hm hu hv hw
  have HT := coreTail_regular_of_valid hR HV
  have HC := (contDiffAt_projectiveCycle 2 hH).comp Y HT.2.1
  have HE := entranceReturn_regular hk hm hu hv hw
  have Htime : ContDiffAt ℝ 2 (fun Z => entranceReturnTime (projectiveCycle (coreTailState h Z))) Y :=
    ContDiffAt.comp (g := entranceReturnTime) (f := projectiveCycle ∘ coreTailState h) Y HE.2.1 HC
  have Hstate : ContDiffAt ℝ 2 (fun Z => entranceReturnState (projectiveCycle (coreTailState h Z))) Y :=
    ContDiffAt.comp (g := entranceReturnState) (f := projectiveCycle ∘ coreTailState h) Y HE.2.2.1 HC
  exact ⟨HT.1.add Htime, Hstate⟩


/-- The cyclic tail and long entrance compose to the first physical arrival of the next active wall. -/
theorem solution {εin η : ℝ} (hεin : 0 < εin ∧ εin ≤ 1 / 10000)
    (hη : 0 < η ∧ η ≤ 1 / 100) {q J : ℕ} (hJ : q + 2 ≤ J)
    (hηin : η ≤ εin / (4 * (11 / 5) ^ q)) :
    ∃ ε > (0 : ℝ), ∀ α b u w : ℝ,
      (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ (2 * J) →
      |u| + |w| ≤ b → 0 < u → 0 < w →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      let z := projectiveCycle (coreTailState h Y)
      let k := coreRadius (z 0) (z 2)
      let x := axisCycle (fromProjectiveState (coreTailEntry Y))
      let T := terminalConnectionTime h Y
      coreTailValid h Y ∧ entranceReturnValid z ∧
        (z 1 * k ^ q ≤ εin / 2 ∧ z 3 * k ^ q ≤ εin / 2) ∧
        ContDiffAt ℝ 2 entranceReturnTime z ∧ ContDiffAt ℝ 2 entranceReturnState z ∧
        IsLeast {t : ℝ | 0 < t ∧ t ∈ normalizedMaxDomain x 0 ∧
          projectiveActiveWall (normalizedMaxCurve x 0 t) = 1} T ∧
        (∀ t ∈ Icc 0 T, 0 < 1 + normalizedMaxCurve x 0 t 0) ∧
        (∀ t ∈ Ico 0 T, projectiveActiveWall (normalizedMaxCurve x 0 t) < 1) ∧
        toProjectiveState (normalizedMaxCurve x 0 T) = terminalConnectionState h Y ∧
        terminalConnectionState h Y 2 = 1 ∧
        0 < normalizedEventRate projectiveActiveWall x 0 T ∧
        ContDiffAt ℝ 2 (terminalConnectionTime h) Y ∧ ContDiffAt ℝ 2 (terminalConnectionState h) Y := by
  obtain ⟨ε, hε, HE⟩ := exists_terminal_cycle_entrance_inputs hεin.1 hη hJ hηin
  refine ⟨ε, hε, ?_⟩
  intro α b u w hα hb hsmall hsum hu hw Y h z k x T
  obtain ⟨HV, HEq, HK, HM, HU, HVa, HW, HF, HH⟩ := HE α b u w hα hb hsmall hsum hu hw
  have hc : stateConstraint x = 1 := by
    rw [axisCycle_constraint]
    exact fromProjectiveState_constraint (coreTailValid_denom_pos HV).ne'
  have H := entranceReturn_existing_orbit hc HV.1.1.1.le HEq
    (fun r hr => ⟨(HF r hr).1, by
      have Hb := (HF r hr).2
      change toProjectiveState (normalizedMaxCurve x 0 r) 2 < 1
      linarith only [le_abs_self (toProjectiveState (normalizedMaxCurve x 0 r) 2), Hb]⟩)
    HK.le (by linarith only [HM]) ⟨HU.1.le, HU.2.1.trans hεin.2⟩
    ⟨HVa.1, by linarith only [HVa.2]⟩ ⟨HW.1.le, HW.2.1.trans hεin.2⟩
  have Hstate : toProjectiveState (normalizedMaxCurve x 0 T) = terminalConnectionState h Y := H.2.2.2.2.2.2.1
  have Hregular := terminalConnection_regular_of_entrance (by change 1 < 2 + 2 * α; linarith only [hα.1]) HV HH.ne'
    HK.le (by linarith only [HM]) ⟨HU.1.le, HU.2.1.trans hεin.2⟩
    ⟨HVa.1, by linarith only [HVa.2]⟩ ⟨HW.1.le, HW.2.1.trans hεin.2⟩
  refine ⟨HV, H.1, ⟨HU.2.2, HW.2.2⟩, H.2.1, H.2.2.1,
    H.2.2.2.1, H.2.2.2.2.1, H.2.2.2.2.2.1, Hstate, ?_, H.2.2.2.2.2.2.2, Hregular⟩
  rw [← Hstate]
  exact H.2.2.2.1.1.2.2
