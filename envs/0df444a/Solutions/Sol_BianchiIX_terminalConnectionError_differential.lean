-- Prove2me | solution 1 for BianchiIX.terminalConnectionError_differential
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T19:38:53.266298+00:00
-- url     : https://prove2.me/submissions/145df647-31e7-4a95-b70a-b2a9a6a22f18

import Definitions.Def_BianchiIX_EntrancePhaseResponseData
import Definitions.Def_BianchiIX_TerminalConeData
import Theorems.Thm_BianchiIX_coreTail_regular_of_valid
import Theorems.Thm_BianchiIX_terminalEntranceInput_fderiv
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
import Mathlib.Topology.Order.ProjIcc
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

noncomputable section
open BianchiIX
open Filter
open scoped Topology

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

private theorem BianchiIX.terminalConnectionError_chart_germ {h : ℝ} {Y : ExitTailState}
    {Ψ : ProjectiveState → ProjectiveState} (HΨ : EntranceRadialInverseAt (terminalCyclicInput h Y) Ψ)
    (hc : ContinuousAt (terminalCyclicInput h) Y) :
    terminalConnectionError h =ᶠ[𝓝 Y] (fun Z =>
      coreRadius (entranceReturnState (Ψ (terminalEntranceInput h Z)) 0)
        (entranceReturnState (Ψ (terminalEntranceInput h Z)) 2) - terminalEntranceInput h Z 0) := by
  filter_upwards [hc.tendsto.eventually HΨ.left_inverse] with Z hZ
  change terminalConnectionPhase h Z - terminalEntranceInput h Z 0 = _
  change Ψ (terminalEntranceInput h Z) = terminalCyclicInput h Z at hZ
  rw [hZ]
  rfl


/-- The four entrance columns compose to the actual terminal phase error at fixed auxiliary height. -/
theorem solution {h : ℝ} {Y : ExitTailState}
    (hR : 1 < Y 0) (HV : coreTailValid h Y) (hh : 0 < h)
    (hH : 0 < projectiveCycleDenom (coreTailState h Y))
    (hc : ContDiffAt ℝ 2 (terminalEntranceInput h) Y)
    {Ψ : ProjectiveState → ProjectiveState} (HΨ : EntranceRadialInverseAt (terminalCyclicInput h Y) Ψ)
    (hF : ContDiffAt ℝ 2 (fun z => coreRadius (entranceReturnState (Ψ z) 0)
      (entranceReturnState (Ψ z) 2)) (terminalEntranceInput h Y)) :
    ContDiffAt ℝ 2 (terminalConnectionError h) Y ∧ ∀ v : ExitTailState,
      let z := terminalEntranceInput h Y
      let F := fun z => coreRadius (entranceReturnState (Ψ z) 0) (entranceReturnState (Ψ z) 2)
      fderiv ℝ (terminalConnectionError h) Y v =
        (fderiv ℝ F z (Pi.single 0 1) - 1) * fderiv ℝ (fun Z => terminalEntranceInput h Z 0) Y v +
        fderiv ℝ F z (Pi.single 1 1) * (z 1 * fderiv ℝ (fun Z => Real.log (terminalEntranceInput h Z 1)) Y v) +
        fderiv ℝ F z (Pi.single 2 1) * (v 2 * terminalWallFactor h Y 1 + z 2 *
          fderiv ℝ (fun Z => Real.log (terminalWallFactor h Z 1)) Y v) +
        fderiv ℝ F z (Pi.single 3 1) * (v 1 * terminalWallFactor h Y 0 + z 3 *
          fderiv ℝ (fun Z => Real.log (terminalWallFactor h Z 0)) Y v) := by
  let F := fun z => coreRadius (entranceReturnState (Ψ z) 0) (entranceReturnState (Ψ z) 2)
  have Htail := (coreTail_regular_of_valid hR HV).2.1
  have Hcyc : ContDiffAt ℝ 2 (terminalCyclicInput h) Y :=
    ContDiffAt.comp (g := projectiveCycle) (f := coreTailState h) Y
      (contDiffAt_projectiveCycle 2 hH.ne') Htail
  have HE := terminalConnectionError_chart_germ HΨ Hcyc.continuousAt
  have Hr : ContDiffAt ℝ 2 (fun Z => terminalEntranceInput h Z 0) Y := (contDiffAt_pi.mp hc) 0
  have Hreg := (ContDiffAt.comp (g := F) (f := terminalEntranceInput h) Y hF hc).sub Hr
  refine ⟨Hreg.congr_of_eventuallyEq HE, ?_⟩
  intro v z F
  have HD := ((hF.differentiableAt (by norm_num)).hasFDerivAt.comp Y
    (hc.differentiableAt (by norm_num)).hasFDerivAt).sub (Hr.differentiableAt (by norm_num)).hasFDerivAt
  change HasFDerivAt (fun Z => coreRadius (entranceReturnState (Ψ (terminalEntranceInput h Z)) 0)
    (entranceReturnState (Ψ (terminalEntranceInput h Z)) 2) - terminalEntranceInput h Z 0) _ Y at HD
  rw [HE.fderiv_eq, HD.fderiv]
  simp only [sub_apply, ContinuousLinearMap.comp_apply]
  rw [terminalEntranceInput_fderiv hR HV hh hH hc v]
  have Hlin (a b c d : ℝ) : fderiv ℝ F z ![a, b, c, d] =
      a * fderiv ℝ F z (Pi.single 0 1) + b * fderiv ℝ F z (Pi.single 1 1) +
      c * fderiv ℝ F z (Pi.single 2 1) + d * fderiv ℝ F z (Pi.single 3 1) := by
    have H : (![a, b, c, d] : ProjectiveState) =
        a • Pi.single 0 1 + b • Pi.single 1 1 + c • Pi.single 2 1 + d • Pi.single 3 1 := by
      ext i
      fin_cases i <;> simp
    rw [H, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul]
    rfl
  rw [Hlin]
  ring
