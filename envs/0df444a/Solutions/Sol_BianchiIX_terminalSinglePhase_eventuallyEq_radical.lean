-- Prove2me | solution 1 for BianchiIX.terminalSinglePhase_eventuallyEq_radical
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T19:30:50.077453+00:00
-- url     : https://prove2.me/submissions/ea00b788-2f9f-400b-a171-c63bf681eb15

import Definitions.Def_BianchiIX_TerminalConeData
import Theorems.Thm_BianchiIX_coreTail_regular_of_valid
import Theorems.Thm_BianchiIX_exitSinglePhase_eq_singleStrongPhase
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
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Module
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
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Order.ProjIcc
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp

noncomputable section
open BianchiIX
open Filter
open scoped Topology

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreRadius_sq (m v : ℝ) : coreRadius m v ^ 2 = coreEnergy m v :=
  Real.sq_sqrt (by unfold coreEnergy; positivity)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTailGap_of_coreRadius {m v : ℝ} (hm : m < 1) :
    exitTailGap (coreRadius m v) v = 1 - m := by
  unfold exitTailGap
  rw [coreRadius_sq]
  dsimp only [coreEnergy]
  rw [add_sub_cancel_right, Real.sqrt_sq_eq_abs, abs_of_neg (by linarith only [hm] : m - 1 < 0)]
  ring

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.fromExitTailState_toExitTailState {y : ProjectiveState} (hm : y 0 < 1) :
    fromExitTailState (y 2) (toExitTailState y) = y := by
  ext i
  fin_cases i
  · change 1 - exitTailGap (coreRadius (y 0) (y 2)) (y 2) = y 0
    rw [exitTailGap_of_coreRadius hm]
    ring
  · rfl
  · rfl
  · rfl

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.coreTailState_active {η : ℝ} {Y : CoreAngleState} (hvalid : coreTailValid η Y) :
    coreTailState η Y 2 = η := hvalid.1.1.2.2

end
end


/-- The cyclic single-wall phase and its fixed-height radical agree on a full entrance neighborhood. -/
theorem solution {h : ℝ} {Y : ExitTailState}
    (hR : 1 < Y 0) (HV : coreTailValid h Y) (hm : coreTailState h Y 0 < 1)
    (hF : ContinuousAt (fun Z => toExitTailState (coreTailState h Z)) Y)
    (hsq : h ^ 2 < (toExitTailState (coreTailState h Y) 0) ^ 2)
    (hB : 0 < exitSingleBase (toExitTailState (coreTailState h Y) 0) h)
    (hD : 0 < exitSingleBase (toExitTailState (coreTailState h Y) 0) h +
      exitSingleDefect (toExitTailState (coreTailState h Y) 1) h (toExitTailState (coreTailState h Y) 2))
    (hN : 0 < (toExitTailState (coreTailState h Y) 0) ^ 2 - 4 +
      exitSingleDefect (toExitTailState (coreTailState h Y) 1) h (toExitTailState (coreTailState h Y) 2)) :
    terminalSinglePhase h =ᶠ[𝓝 Y] (fun Z =>
      exitSinglePhase (toExitTailState (coreTailState h Z) 0) (coreTailState h Z 1) h (coreTailState h Z 3)) := by
  let F := fun Z => toExitTailState (coreTailState h Z)
  have Hcore := coreTail_regular_of_valid hR HV
  have Hm : ∀ᶠ Z in 𝓝 Y, coreTailState h Z 0 < 1 :=
    ((continuous_apply 0).continuousAt.comp Hcore.2.1.continuousAt).eventually (isOpen_Iio.mem_nhds hm)
  have HA : Continuous (fun Q : ExitTailState => (Q 0) ^ 2 - h ^ 2) := by fun_prop
  have HB : Continuous (fun Q : ExitTailState => exitSingleBase (Q 0) h) := by
    unfold exitSingleBase exitTailGap; fun_prop
  have HT : Continuous (fun Q : ExitTailState => exitSingleDefect (Q 1) h (Q 2)) := by
    unfold exitSingleDefect; fun_prop
  have HD : Continuous (fun Q : ExitTailState => exitSingleBase (Q 0) h + exitSingleDefect (Q 1) h (Q 2)) := HB.add HT
  have HN : Continuous (fun Q : ExitTailState => (Q 0) ^ 2 - 4 + exitSingleDefect (Q 1) h (Q 2)) := by fun_prop
  have Ha := (HA.continuousAt.comp hF).eventually (isOpen_Ioi.mem_nhds (sub_pos.mpr hsq))
  have Hb := (HB.continuousAt.comp hF).eventually (isOpen_Ioi.mem_nhds hB)
  have Hd := (HD.continuousAt.comp hF).eventually (isOpen_Ioi.mem_nhds hD)
  have Hn := (HN.continuousAt.comp hF).eventually (isOpen_Ioi.mem_nhds hN)
  filter_upwards [Hcore.2.2, Hm, Ha, Hb, Hd, Hn] with Z hv hmZ ha hb hd hn
  let Q := F Z
  have Hactive := coreTailState_active hv
  have Hrec : fromExitTailState h Q = coreTailState h Z := by
    conv_lhs => rw [← Hactive]
    exact fromExitTailState_toExitTailState hmZ
  have HE := exitSinglePhase_eq_singleStrongPhase (sub_pos.mp ha).le hb hd hn
  change exitSinglePhase (Q 0) (Q 1) h (Q 2) = _ at HE
  change singleStrongPhase (projectiveCycle (coreTailState h Z) 0)
    (projectiveCycle (coreTailState h Z) 1) = exitSinglePhase (Q 0) (Q 1) h (Q 2)
  rw [← Hrec]
  convert HE.symm using 1
  dsimp [projectiveCycle, projectiveCycleDenom, fromExitTailState]
  congr 2; ring
