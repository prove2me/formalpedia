-- Prove2me | solution 1 for BianchiIX.fromExitTailState_fderiv_bound
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T18:59:41.907089+00:00
-- url     : https://prove2.me/submissions/04f0001e-7b46-453f-b8b3-1a9ef5236852

import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_TerminalConnectionData
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

noncomputable section
open BianchiIX
open Filter
open scoped Topology

section
noncomputable section
open BianchiIX

private theorem BianchiIX.fderiv_norm_le_of_coordinate_bounds {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {f : E → Fin n → ℝ} {x : E} {C : ℝ} (hC : 0 ≤ C)
    (hf : DifferentiableAt ℝ f x) (hbound : ∀ i, ‖fderiv ℝ (fun y => f y i) x‖ ≤ C) :
    ‖fderiv ℝ f x‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro v
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC (norm_nonneg v))).mpr
  intro i
  have heq := congrArg (fun L : E →L[ℝ] ℝ => L v) (fderiv_apply hf i)
  change fderiv ℝ (fun y => f y i) x v = (fderiv ℝ f x v) i at heq
  rw [← heq]
  exact ((fderiv ℝ (fun y => f y i) x).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (hbound i) (norm_nonneg v))

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTailGap_sq {R v : ℝ} (h : v ^ 2 ≤ R ^ 2) :
    exitTailGap R v ^ 2 = R ^ 2 - v ^ 2 := Real.sq_sqrt (sub_nonneg.mpr h)

end
end


/-- At fixed height, reconstruction of the descending shear costs at most a factor two. -/
theorem solution {h : ℝ} {Y : ExitTailState}
    (hR : 7 / 4 ≤ Y 0) (hh : |h| ≤ 1) :
    ContDiffAt ℝ 2 (fromExitTailState h) Y ∧ ‖fderiv ℝ (fromExitTailState h) Y‖ ≤ 2 := by
  have hR0 : 0 < Y 0 := by linarith only [hR]
  have hR2 := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 7 / 4) hR0.le).mpr hR
  have hh2 : h ^ 2 ≤ 1 := by nlinarith only [sq_abs h, sq_nonneg (|h| - 1), hh, abs_nonneg h]
  have hgap : h ^ 2 < (Y 0) ^ 2 := by nlinarith only [hR2, hh2]
  have hg0 : 0 < exitTailGap (Y 0) h := Real.sqrt_pos.mpr (sub_pos.mpr hgap)
  have hratio : |Y 0 / exitTailGap (Y 0) h| ≤ 2 := by
    rw [abs_of_pos (div_pos hR0 hg0)]
    apply (div_le_iff₀ hg0).mpr
    nlinarith only [exitTailGap_sq hgap.le, hR2, hh2, hg0, hR0]
  have hgapreg : ContDiffAt ℝ 2 (fun Z : ExitTailState => exitTailGap (Z 0) h) Y := by
    unfold exitTailGap
    have H0 : ContDiffAt ℝ 2 (fun Z : ExitTailState => Z 0) Y := by fun_prop
    exact ((H0.pow 2).sub contDiffAt_const).sqrt
      (sub_pos.mpr hgap).ne'
  have Hreg : ContDiffAt ℝ 2 (fromExitTailState h) Y := by
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i
    · exact contDiffAt_const.sub hgapreg
    all_goals dsimp [fromExitTailState]; fun_prop
  have Hsqrt := (((hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) Y).pow 2).sub_const (h ^ 2)).sqrt
    (sub_pos.mpr hgap).ne'
  have HM := (hasFDerivAt_const (1 : ℝ) Y).sub Hsqrt
  change HasFDerivAt (fun Z : ExitTailState => 1 - exitTailGap (Z 0) h) _ Y at HM
  have Hformula (v : ExitTailState) :
      fderiv ℝ (fun Z : ExitTailState => 1 - exitTailGap (Z 0) h) Y v =
        -(Y 0 / exitTailGap (Y 0) h) * v 0 := by
    rw [HM.fderiv]
    simp only [sub_apply, zero_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
    unfold exitTailGap
    ring
  refine ⟨Hreg, fderiv_norm_le_of_coordinate_bounds (by norm_num)
    (Hreg.differentiableAt (by norm_num)) ?_⟩
  intro i
  fin_cases i
  · apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro v
    change |fderiv ℝ (fun Z : ExitTailState => 1 - exitTailGap (Z 0) h) Y v| ≤ _
    rw [Hformula, abs_mul, abs_neg]
    exact mul_le_mul hratio (norm_le_pi_norm v 0) (abs_nonneg _) (by norm_num)
  · change ‖fderiv ℝ (fun Z : ExitTailState => Z 1) Y‖ ≤ 2
    rw [(hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 3) Y).fderiv]
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro v
    exact (norm_le_pi_norm v 1).trans (by nlinarith only [norm_nonneg v])
  · change ‖fderiv ℝ (fun _ : ExitTailState => h) Y‖ ≤ 2
    simp
  · change ‖fderiv ℝ (fun Z : ExitTailState => Z 2) Y‖ ≤ 2
    rw [(hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 3) Y).fderiv]
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro v
    exact (norm_le_pi_norm v 2).trans (by nlinarith only [norm_nonneg v])
