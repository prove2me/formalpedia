-- Prove2me | solution 1 for BianchiIX.terminalEntranceInput_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T19:02:36.348893+00:00
-- url     : https://prove2.me/submissions/a3cc773d-ae8f-4ef8-bb0d-a594ff8e19ce

import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Dynamics_ProjectiveWallMultipliers
import Definitions.Def_BianchiIX_Dynamics_CoreTailMultipliers
import Definitions.Def_BianchiIX_TerminalConeData
import Theorems.Thm_BianchiIX_contDiffAt_coreTailMultiplier_two
import Theorems.Thm_BianchiIX_coreTailMultiplier_formula
import Theorems.Thm_BianchiIX_coreTail_regular_of_valid
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
open Set MeasureTheory

private theorem BianchiIX.normalizedProjectiveWallMultiplier_pos (x : NormalizedState) (T : ℝ) (i : Fin 3) :
    0 < normalizedProjectiveWallMultiplier x T i := Real.exp_pos _

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

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.coreTailMultiplier_pos (η : ℝ) (Y : CoreAngleState) (i : Fin 2) :
    0 < coreTailMultiplier η Y i := normalizedProjectiveWallMultiplier_pos _ _ _

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.terminalWallFactor_pos {h : ℝ} {Y : ExitTailState}
    (hH : 0 < projectiveCycleDenom (coreTailState h Y)) (i : Fin 2) :
    0 < terminalWallFactor h Y i :=
  div_pos (mul_pos (by norm_num) (coreTailMultiplier_pos h Y i)) hH

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.terminalEntranceInput_wall_factors {h : ℝ} {Y : ExitTailState} (HV : coreTailValid h Y) :
    terminalEntranceInput h Y 1 = 4 * h / projectiveCycleDenom (coreTailState h Y) ∧
      terminalEntranceInput h Y 2 = Y 2 * terminalWallFactor h Y 1 ∧
      terminalEntranceInput h Y 3 = Y 1 * terminalWallFactor h Y 0 := by
  have H0 := coreTailMultiplier_formula HV 0
  have H1 := coreTailMultiplier_formula HV 1
  change coreTailState h Y 1 = Y 1 * coreTailMultiplier h Y 0 at H0
  change coreTailState h Y 3 = Y 2 * coreTailMultiplier h Y 1 at H1
  change (4 * coreTailState h Y 2 / _ = _) ∧ (4 * coreTailState h Y 3 / _ = _) ∧
    (4 * coreTailState h Y 1 / _ = _)
  rw [coreTailState_active HV, H0, H1]
  dsimp only [terminalWallFactor]
  constructor
  · rfl
  · constructor <;> ring

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_terminalWallFactor_two {h : ℝ} {Y : ExitTailState}
    (hR : 1 < Y 0) (HV : coreTailValid h Y)
    (hH : 0 < projectiveCycleDenom (coreTailState h Y)) (i : Fin 2) :
    ContDiffAt ℝ 2 (fun Z => terminalWallFactor h Z i) Y ∧
      ContDiffAt ℝ 2 (fun Z => Real.log (terminalWallFactor h Z i)) Y := by
  have HR := coreTail_regular_of_valid hR HV
  have HM := (contDiffAt_coreTailMultiplier_two hR HV HR.1 i).1
  have HD : ContDiffAt ℝ 2 (fun Z => projectiveCycleDenom (coreTailState h Z)) Y :=
    ContDiffAt.comp (g := projectiveCycleDenom) (f := coreTailState h) Y
    (contDiff_projectiveCycleDenom 2).contDiffAt HR.2.1
  have HB : ContDiffAt ℝ 2 (fun Z => terminalWallFactor h Z i) Y :=
    (contDiffAt_const.mul HM).div HD hH.ne'
  exact ⟨HB, HB.log (terminalWallFactor_pos hH i).ne'⟩

end
end


theorem solution {h : ℝ} {Y : ExitTailState}
    (hR : 1 < Y 0) (HV : coreTailValid h Y) (hh : 0 < h)
    (hH : 0 < projectiveCycleDenom (coreTailState h Y))
    (hc : ContDiffAt ℝ 2 (terminalEntranceInput h) Y) (v : ExitTailState) :
    fderiv ℝ (terminalEntranceInput h) Y v =
      ![fderiv ℝ (fun Z => terminalEntranceInput h Z 0) Y v,
        terminalEntranceInput h Y 1 * fderiv ℝ (fun Z => Real.log (terminalEntranceInput h Z 1)) Y v,
        v 2 * terminalWallFactor h Y 1 + terminalEntranceInput h Y 2 *
          fderiv ℝ (fun Z => Real.log (terminalWallFactor h Z 1)) Y v,
        v 1 * terminalWallFactor h Y 0 + terminalEntranceInput h Y 3 *
          fderiv ℝ (fun Z => Real.log (terminalWallFactor h Z 0)) Y v] := by
  have hd := hc.differentiableAt (by norm_num)
  have Hnear := (coreTail_regular_of_valid hR HV).2.2
  have Hwall (i : Fin 2) :
      fderiv ℝ (terminalEntranceInput h) Y v (if i = 0 then 3 else 2) =
        v i.succ * terminalWallFactor h Y i +
        terminalEntranceInput h Y (if i = 0 then 3 else 2) *
          fderiv ℝ (fun Z => Real.log (terminalWallFactor h Z i)) Y v := by
    have hm := (contDiffAt_terminalWallFactor_two hR HV hH i).1.differentiableAt (by norm_num)
    have HE : (fun Z => terminalEntranceInput h Z (if i = 0 then 3 else 2)) =ᶠ[𝓝 Y]
        (fun Z => Z i.succ * terminalWallFactor h Z i) := by
      filter_upwards [Hnear] with Z hZ
      fin_cases i
      · exact (terminalEntranceInput_wall_factors hZ).2.2
      · exact (terminalEntranceInput_wall_factors hZ).2.1
    have HD := (hasFDerivAt_apply (𝕜 := ℝ) i.succ Y).mul hm.hasFDerivAt
    have H := congrArg (fun L : ExitTailState →L[ℝ] ℝ => L v) (HE.fderiv_eq.trans HD.fderiv)
    rw [fderiv_apply hd] at H
    have HM : fderiv ℝ (fun Z => terminalWallFactor h Z i) Y v = terminalWallFactor h Y i *
        fderiv ℝ (fun Z => Real.log (terminalWallFactor h Z i)) Y v := by
      rw [(hm.hasFDerivAt.log (terminalWallFactor_pos hH i).ne').fderiv]
      simp only [smul_apply, smul_eq_mul]
      field_simp [(terminalWallFactor_pos hH i).ne']
    have HEY : terminalEntranceInput h Y (if i = 0 then 3 else 2) = Y i.succ * terminalWallFactor h Y i := HE.self_of_nhds
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      add_apply, smul_apply, smul_eq_mul] at H
    rw [H, HM, HEY]
    ring
  ext i
  fin_cases i
  · exact (congrArg (fun L : ExitTailState →L[ℝ] ℝ => L v) (fderiv_apply hd 0)).symm
  · have hf := (hasFDerivAt_pi'.mp hd.hasFDerivAt 1)
    change fderiv ℝ (terminalEntranceInput h) Y v 1 = terminalEntranceInput h Y 1 *
      fderiv ℝ (fun Z => Real.log (terminalEntranceInput h Z 1)) Y v
    have hp : 0 < terminalEntranceInput h Y 1 := by
      rw [(terminalEntranceInput_wall_factors HV).1]
      exact div_pos (mul_pos (by norm_num) hh) hH
    rw [(hf.log hp.ne').fderiv]
    simp only [smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
    field_simp [hp.ne']
  · exact Hwall 1
  · exact Hwall 0
