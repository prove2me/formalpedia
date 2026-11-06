-- Prove2me | solution 1 for BianchiIX.exists_terminalCyclicInput_derivative_uniform
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T23:24:26.954653+00:00
-- url     : https://prove2.me/submissions/e8fe75f8-0483-492b-aa08-3505f560d5c2

import Definitions.Def_BianchiIX_TerminalConnectionData
import Definitions.Def_BianchiIX_Dynamics_AxisMaps
import Definitions.Def_BianchiIX_TerminalConeData
import Theorems.Thm_BianchiIX_coreTailValid_of_height_le
import Theorems.Thm_BianchiIX_coreTail_regular_of_valid
import Theorems.Thm_BianchiIX_exists_terminal_axisCycle_regular
import Theorems.Thm_BianchiIX_exists_terminal_exitReturn_two_bounds_uniform
import Theorems.Thm_BianchiIX_fromExitTailState_fderiv_bound
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
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Order.ProjIcc
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp

noncomputable section
open BianchiIX

section
noncomputable section
open BianchiIX
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem BianchiIX.hasDerivAt_fderiv_apply_const {f : E → F} {gamma : ℝ → E} {v : E} {t : ℝ}
    (hf : DifferentiableAt ℝ (fderiv ℝ f) (gamma t))
    (hg : HasDerivAt gamma v t) (w : E) :
    HasDerivAt (fun s => fderiv ℝ f (gamma s) w)
      (fderiv ℝ (fderiv ℝ f) (gamma t) v w) t := by
  have H := (hf.hasFDerivAt.comp_hasDerivAt t hg).clm_apply (hasDerivAt_const t w)
  simpa only [Function.comp_apply, ContinuousLinearMap.map_zero, add_zero] using H

end
end

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
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem BianchiIX.clm_norm_le_card_mul_basis_bound {n : ℕ} (L : (Fin n → ℝ) →L[ℝ] F)
    {C : ℝ} (hC : 0 ≤ C) (hL : ∀ i, ‖L (Pi.single i 1)‖ ≤ C) : ‖L‖ ≤ n * C := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have hv : (∑ i : Fin n, v i • (Pi.single i 1 : Fin n → ℝ)) = v := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have HL : L v = ∑ i : Fin n, v i • L (Pi.single i 1) := by
    rw [← hv, map_sum]
    simp only [map_smul, hv]
  calc
    ‖L v‖ = ‖∑ i : Fin n, v i • L (Pi.single i 1)‖ := congrArg norm HL
    _ ≤ ∑ i : Fin n, ‖v i • L (Pi.single i 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, ‖v‖ * C := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_mul (norm_le_pi_norm v i) (hL i) (norm_nonneg _) (norm_nonneg v)
    _ = (n : ℝ) * C * ‖v‖ := by simp; ring

end
end

section
noncomputable section
open BianchiIX
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem BianchiIX.bilinear_norm_le_card_mul_basis_bound {n m : ℕ}
    (L : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ) →L[ℝ] F) {C : ℝ}
    (hC : 0 ≤ C) (hL : ∀ i j, ‖L (Pi.single i 1) (Pi.single j 1)‖ ≤ C) :
    ‖L‖ ≤ (n : ℝ) * m * C := by
  have H := clm_norm_le_card_mul_basis_bound L (C := m * C) (by positivity)
    (fun i => clm_norm_le_card_mul_basis_bound (L (Pi.single i 1)) hC (hL i))
  simpa only [mul_assoc] using H

end
end

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

private theorem BianchiIX.exitTailGap_sq {R v : ℝ} (h : v ^ 2 ≤ R ^ 2) :
    exitTailGap R v ^ 2 = R ^ 2 - v ^ 2 := Real.sq_sqrt (sub_nonneg.mpr h)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTailGap_terminal_offset {α B R v : ℝ} (hα : 0 < α ∧ α ≤ 1)
    (hB : B ≤ α / 10000) (hR : |R - (2 + 2 * α)| ≤ B) (hv : 0 ≤ v ∧ v ≤ α / 100) :
    199 / 100 * α < exitTailGap R v - 2 ∧ exitTailGap R v - 2 < 201 / 100 * α := by
  have hα0 : 0 < α := hα.1
  have hRc := abs_le.mp hR
  have hRlo : 2 + 19999 / 10000 * α ≤ R := by linarith only [hRc.1, hB]
  have hR0 : 0 ≤ R := by linarith only [hRlo, hα.1]
  have hRsq := (sq_le_sq₀ (by positivity) hR0).mpr hRlo
  have hvsq := (sq_le_sq₀ hv.1 (by positivity)).mpr hv.2
  have hvR : v ^ 2 ≤ R ^ 2 := by nlinarith only [hRsq, hvsq, hα.1, sq_nonneg α]
  have ht := exitTailGap_sq hvR
  have ht0 : 0 ≤ exitTailGap R v := Real.sqrt_nonneg _
  have hs : (2 + 199 / 100 * α) ^ 2 < (exitTailGap R v) ^ 2 := by
    nlinarith only [hRsq, hvsq, ht, hα.1, sq_nonneg α]
  have hlo := (sq_lt_sq₀ (by positivity) ht0).mp hs
  have hhi : exitTailGap R v ≤ R := (Real.sqrt_le_left hR0).mpr (by nlinarith only [sq_nonneg v])
  constructor <;> linarith only [hlo, hhi, hRc.2, hB, hα.1]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitCycle_quotient_first_bound {α H n nᵢ Hᵢ : ℝ} (hα : 0 < α)
    (hH : 39 / 10 * α ^ 2 ≤ H) (hn : |n| ≤ 12 * α) (hni : |nᵢ| ≤ 4) (hHi : |Hᵢ| ≤ 6 * α) :
    |nᵢ / H - n * Hᵢ / H ^ 2| ≤ 6 / α ^ 2 := by
  have hH0 : 0 < H := lt_of_lt_of_le (by positivity) hH
  calc
    _ ≤ |nᵢ / H| + |n * Hᵢ / H ^ 2| := abs_sub _ _
    _ = |nᵢ| / H + |n| * |Hᵢ| / H ^ 2 := by simp only [abs_div, abs_mul, abs_pow, abs_of_pos hH0]
    _ ≤ 4 / H + (12 * α) * (6 * α) / H ^ 2 := by gcongr
    _ ≤ 4 / (39 / 10 * α ^ 2) + (12 * α) * (6 * α) / (39 / 10 * α ^ 2) ^ 2 := by gcongr
    _ = (2920 / 507 : ℝ) / α ^ 2 := by field_simp; ring
    _ ≤ 6 / α ^ 2 := div_le_div_of_nonneg_right (by norm_num) (sq_nonneg α)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitCycle_quotient_second_bound {α H n nᵢ nⱼ Hᵢ Hⱼ Hᵢⱼ : ℝ} (hα : 0 < α)
    (hH : 39 / 10 * α ^ 2 ≤ H) (hn : |n| ≤ 12 * α)
    (hni : |nᵢ| ≤ 4) (hnj : |nⱼ| ≤ 4) (hHi : |Hᵢ| ≤ 6 * α) (hHj : |Hⱼ| ≤ 6 * α)
    (hHij : |Hᵢⱼ| ≤ 2) :
    |-(nᵢ * Hⱼ + nⱼ * Hᵢ + n * Hᵢⱼ) / H ^ 2 + 2 * n * Hᵢ * Hⱼ / H ^ 3| ≤ 20 / α ^ 3 := by
  have hH0 : 0 < H := lt_of_lt_of_le (by positivity) hH
  have Hsum : |nᵢ * Hⱼ + nⱼ * Hᵢ + n * Hᵢⱼ| ≤ 72 * α := by
    have H1 := abs_add_le (nᵢ * Hⱼ + nⱼ * Hᵢ) (n * Hᵢⱼ)
    have H2 := abs_add_le (nᵢ * Hⱼ) (nⱼ * Hᵢ)
    simp only [abs_mul] at H1 H2
    have H3 := mul_le_mul hni hHj (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 4)
    have H4 := mul_le_mul hnj hHi (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 4)
    have H5 := mul_le_mul hn hHij (abs_nonneg _) (by positivity : 0 ≤ 12 * α)
    linarith only [H1, H2, H3, H4, H5]
  calc
    _ ≤ |-(nᵢ * Hⱼ + nⱼ * Hᵢ + n * Hᵢⱼ) / H ^ 2| + |2 * n * Hᵢ * Hⱼ / H ^ 3| := abs_add_le _ _
    _ = |nᵢ * Hⱼ + nⱼ * Hᵢ + n * Hᵢⱼ| / H ^ 2 + 2 * |n| * |Hᵢ| * |Hⱼ| / H ^ 3 := by
      simp only [abs_div, abs_neg, abs_mul, abs_pow, abs_of_pos hH0, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ 72 * α / H ^ 2 + 2 * (12 * α) * (6 * α) * (6 * α) / H ^ 3 := by gcongr
    _ ≤ 72 * α / (39 / 10 * α ^ 2) ^ 2 +
        2 * (12 * α) * (6 * α) * (6 * α) / (39 / 10 * α ^ 2) ^ 3 := by gcongr
    _ = (42400 / 2197 : ℝ) / α ^ 3 := by field_simp; ring
    _ ≤ 20 / α ^ 3 := div_le_div_of_nonneg_right (by norm_num) (pow_nonneg hα.le 3)

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
open scoped Topology

private theorem BianchiIX.projectiveCycle_component (i : Fin 4) (y : ProjectiveState) :
    projectiveCycle y i = (if i = 0 then 1 else 0) + cycleNumerator i y / projectiveCycleDenom y := by
  fin_cases i <;> simp [projectiveCycle, cycleNumerator]
  ring

end
end

section
noncomputable section
open BianchiIX
open scoped Topology

private theorem BianchiIX.hasDerivAt_cycleNumerator {γ : ℝ → ProjectiveState} {v : ProjectiveState} {t : ℝ}
    (hγ : HasDerivAt γ v t) (i : Fin 4) :
    HasDerivAt (fun s => cycleNumerator i (γ s)) (cycleNumeratorSlope i v) t := by
  fin_cases i
  · exact ((hasDerivAt_pi.mp hγ 0).add_const 1).const_mul (-4)
  · exact (hasDerivAt_pi.mp hγ 2).const_mul 4
  · exact (hasDerivAt_pi.mp hγ 3).const_mul 4
  · exact (hasDerivAt_pi.mp hγ 1).const_mul 4

end
end

section
noncomputable section
open BianchiIX
open scoped Topology

private theorem BianchiIX.hasDerivAt_projectiveCycleDenom {γ : ℝ → ProjectiveState} {v : ProjectiveState} {t : ℝ}
    (hγ : HasDerivAt γ v t) :
    HasDerivAt (fun s => projectiveCycleDenom (γ s)) (cycleDenomDifferential (γ t) v) t := by
  have h0 := hasDerivAt_pi.mp hγ 0
  have h1 := hasDerivAt_pi.mp hγ 1
  have h2 := hasDerivAt_pi.mp hγ 2
  have h3 := hasDerivAt_pi.mp hγ 3
  have hquad := ((((h0.add_const 1).pow 2).add (h1.pow 2)).add (h2.pow 2)).add (h3.pow 2)
  have hcross := (((h1.mul h2).add (h1.mul h3)).add (h2.mul h3)).const_mul 2
  have H := hquad.sub hcross
  convert! H using 1
  · funext s
    dsimp [projectiveCycleDenom, axisCycleDenom, curvature]
    ring
  · dsimp [cycleDenomDifferential]
    ring

end
end

section
noncomputable section
open BianchiIX
open scoped Topology

private theorem BianchiIX.projectiveCycleDenom_fderiv (y v : ProjectiveState) :
    fderiv ℝ projectiveCycleDenom y v = cycleDenomDifferential y v := by
  have hl : HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1
    simp
  have hd := ((contDiff_projectiveCycleDenom 1).differentiable (by norm_num) y).hasFDerivAt
  have H := (show HasFDerivAt projectiveCycleDenom (fderiv ℝ projectiveCycleDenom y)
    (y + (0 : ℝ) • v) by simpa using hd).comp_hasDerivAt 0 hl
  simpa only [zero_smul, add_zero] using H.unique (hasDerivAt_projectiveCycleDenom hl)

end
end

section
noncomputable section
open BianchiIX
open scoped Topology

private theorem BianchiIX.hasDerivAt_cycleDenomDifferential {γ : ℝ → ProjectiveState} {v : ProjectiveState} {t : ℝ}
    (hγ : HasDerivAt γ v t) (w : ProjectiveState) :
    HasDerivAt (fun s => cycleDenomDifferential (γ s) w) (cycleDenomHessian v w) t := by
  have h0 := hasDerivAt_pi.mp hγ 0
  have h1 := hasDerivAt_pi.mp hγ 1
  have h2 := hasDerivAt_pi.mp hγ 2
  have h3 := hasDerivAt_pi.mp hγ 3
  have H := (((((h0.add_const 1).const_mul 2).mul_const (w 0)).add
    ((((h1.sub h2).sub h3).const_mul 2).mul_const (w 1))).add
    ((((h2.sub h1).sub h3).const_mul 2).mul_const (w 2))).add
    ((((h3.sub h1).sub h2).const_mul 2).mul_const (w 3))
  convert! H using 1
  dsimp [cycleDenomHessian]
  ring

end
end

section
noncomputable section
open BianchiIX
open scoped Topology

private theorem BianchiIX.hasDerivAt_projectiveCycle_component {γ : ℝ → ProjectiveState} {v : ProjectiveState} {t : ℝ}
    (hγ : HasDerivAt γ v t) (hH : projectiveCycleDenom (γ t) ≠ 0) (i : Fin 4) :
    HasDerivAt (fun s => projectiveCycle (γ s) i) (cycleDifferential i (γ t) v) t := by
  simp only [projectiveCycle_component]
  apply (((hasDerivAt_cycleNumerator hγ i).div (hasDerivAt_projectiveCycleDenom hγ) hH).const_add
    (if i = 0 then 1 else 0)).congr_deriv
  dsimp [cycleDifferential]
  field_simp

end
end

section
noncomputable section
open BianchiIX
open scoped Topology

private theorem BianchiIX.projectiveCycle_fderiv_component {y : ProjectiveState} (hH : projectiveCycleDenom y ≠ 0)
    (i : Fin 4) (v : ProjectiveState) :
    fderiv ℝ (fun z => projectiveCycle z i) y v = cycleDifferential i y v := by
  have hl : HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1
    simp
  have hreg := contDiffAt_pi.mp (contDiffAt_projectiveCycle 1 hH) i
  have H := (show HasFDerivAt (fun z => projectiveCycle z i) (fderiv ℝ (fun z => projectiveCycle z i) y)
    (y + (0 : ℝ) • v) by simpa using (hreg.differentiableAt (by norm_num)).hasFDerivAt).comp_hasDerivAt 0 hl
  simpa only [zero_smul, add_zero] using H.unique (hasDerivAt_projectiveCycle_component hl (by simpa using hH) i)

end
end

section
noncomputable section
open BianchiIX
open scoped Topology

private theorem BianchiIX.hasDerivAt_cycleDifferential {γ : ℝ → ProjectiveState} {v : ProjectiveState} {t : ℝ}
    (hγ : HasDerivAt γ v t) (hH : projectiveCycleDenom (γ t) ≠ 0) (i : Fin 4) (w : ProjectiveState) :
    HasDerivAt (fun s => cycleDifferential i (γ s) w) (cycleHessian i (γ t) v w) t := by
  have hD := hasDerivAt_projectiveCycleDenom hγ
  have H := ((hasDerivAt_const t (cycleNumeratorSlope i w)).div hD hH).sub
    (((hasDerivAt_cycleNumerator hγ i).mul (hasDerivAt_cycleDenomDifferential hγ w)).div
      (hD.pow 2) (pow_ne_zero 2 hH))
  apply H.congr_deriv
  dsimp [cycleHessian]
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX
open scoped Topology

private theorem BianchiIX.projectiveCycle_fderiv2_component {y : ProjectiveState} (hH : projectiveCycleDenom y ≠ 0)
    (i : Fin 4) (v w : ProjectiveState) :
    fderiv ℝ (fderiv ℝ (fun z => projectiveCycle z i)) y v w = cycleHessian i y v w := by
  have hl : HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1
    simp
  have hreg := contDiffAt_pi.mp (contDiffAt_projectiveCycle 2 (y := y + (0 : ℝ) • v) (by simpa using hH)) i
  have hD := (hreg.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num)
  have H := hasDerivAt_fderiv_apply_const hD hl w
  have hnear : ∀ᶠ s : ℝ in 𝓝 0, projectiveCycleDenom (y + s • v) ≠ 0 :=
    (((contDiff_projectiveCycleDenom 0).continuous.continuousAt.comp hl.continuousAt).eventually_ne
      (by simpa using hH))
  have heq : (fun s : ℝ => fderiv ℝ (fun z => projectiveCycle z i) (y + s • v) w) =ᶠ[𝓝 0]
      (fun s => cycleDifferential i (y + s • v) w) := by
    filter_upwards [hnear] with s hs
    exact projectiveCycle_fderiv_component hs i w
  simpa only [zero_smul, add_zero] using (H.congr_of_eventuallyEq heq.symm).unique
    (hasDerivAt_cycleDifferential hl (by simpa using hH) i w)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.cycleNumeratorSlope_basis_bound (i j : Fin 4) :
    |cycleNumeratorSlope i (Pi.single j 1)| ≤ 4 := by
  fin_cases i <;> fin_cases j <;> norm_num [cycleNumeratorSlope, Pi.single_apply, Fin.ext_iff]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.cycleDenomHessian_basis_bound (i j : Fin 4) :
    |cycleDenomHessian (Pi.single i 1) (Pi.single j 1)| ≤ 2 := by
  fin_cases i <;> fin_cases j <;> norm_num [cycleDenomHessian, Pi.single_apply, Fin.ext_iff]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.cycle_terminal_coefficient_bounds {α : ℝ} {y : ProjectiveState}
    (hm : |y 0 + 1| ≤ 3 * α) (hw : |y 1| + |y 2| + |y 3| ≤ 3 * α) :
    (∀ i : Fin 4, |cycleNumerator i y| ≤ 12 * α) ∧
      (∀ j : Fin 4, |cycleDenomDifferential y (Pi.single j 1)| ≤ 6 * α) := by
  have hthree {a b c : ℝ} (hs : |a| + |b| + |c| ≤ 3 * α) : |a - b - c| ≤ 3 * α := by
    linarith only [abs_sub (a - b) c, abs_sub a b, hs]
  have H1 := hthree hw
  have H2 := hthree (a := y 2) (b := y 1) (c := y 3) (by linarith only [hw])
  have H3 := hthree (a := y 3) (b := y 1) (c := y 2) (by linarith only [hw])
  constructor
  · intro i
    fin_cases i <;> norm_num [cycleNumerator, abs_mul] <;>
      linarith only [hm, hw, abs_nonneg (y 1), abs_nonneg (y 2), abs_nonneg (y 3)]
  · intro j
    fin_cases j <;> norm_num [cycleDenomDifferential, Pi.single_apply, Fin.ext_iff, abs_mul] <;>
      linarith only [hm, H1, H2, H3]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.projectiveCycle_terminal_derivative_bounds {α : ℝ} {y : ProjectiveState} (hα : 0 < α)
    (hH : 39 / 10 * α ^ 2 ≤ projectiveCycleDenom y)
    (hm : |y 0 + 1| ≤ 3 * α) (hw : |y 1| + |y 2| + |y 3| ≤ 3 * α) :
    (∀ i j : Fin 4, |fderiv ℝ (fun z => projectiveCycle z i) y (Pi.single j 1)| ≤ 6 / α ^ 2) ∧
      (∀ i j k : Fin 4, |fderiv ℝ (fderiv ℝ (fun z => projectiveCycle z i)) y
        (Pi.single j 1) (Pi.single k 1)| ≤ 20 / α ^ 3) := by
  have hH0 : projectiveCycleDenom y ≠ 0 := (lt_of_lt_of_le (by positivity) hH).ne'
  obtain ⟨HN, HD⟩ := cycle_terminal_coefficient_bounds hm hw
  constructor
  · intro i j
    rw [projectiveCycle_fderiv_component hH0]
    exact exitCycle_quotient_first_bound hα hH (HN i) (cycleNumeratorSlope_basis_bound i j) (HD j)
  · intro i j k
    rw [projectiveCycle_fderiv2_component hH0]
    exact exitCycle_quotient_second_bound hα hH (HN i)
      (cycleNumeratorSlope_basis_bound i j) (cycleNumeratorSlope_basis_bound i k) (HD j) (HD k)
      (cycleDenomHessian_basis_bound j k)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.projectiveCycle_terminal_operator_bounds {α : ℝ} {y : ProjectiveState} (hα : 0 < α)
    (hH : 39 / 10 * α ^ 2 ≤ projectiveCycleDenom y)
    (hm : |y 0 + 1| ≤ 3 * α) (hw : |y 1| + |y 2| + |y 3| ≤ 3 * α) (i : Fin 4) :
    ‖fderiv ℝ (fun z => projectiveCycle z i) y‖ ≤ 24 / α ^ 2 ∧
      ‖fderiv ℝ (fderiv ℝ (fun z => projectiveCycle z i)) y‖ ≤ 320 / α ^ 3 := by
  obtain ⟨H1, H2⟩ := projectiveCycle_terminal_derivative_bounds hα hH hm hw
  constructor
  · convert clm_norm_le_card_mul_basis_bound (fderiv ℝ (fun z => projectiveCycle z i) y)
      (by positivity : 0 ≤ 6 / α ^ 2) (H1 i) using 1
    norm_num
    ring
  · convert bilinear_norm_le_card_mul_basis_bound (fderiv ℝ (fderiv ℝ (fun z => projectiveCycle z i)) y)
      (by positivity : 0 ≤ 20 / α ^ 3) (H2 i) using 1
    norm_num
    ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.projectiveCycle_log_denom_derivative_bound {α : ℝ} {y : ProjectiveState} (hα : 0 < α)
    (hH : 39 / 10 * α ^ 2 ≤ projectiveCycleDenom y)
    (hm : |y 0 + 1| ≤ 3 * α) (hw : |y 1| + |y 2| + |y 3| ≤ 3 * α) :
    ‖fderiv ℝ (fun z => Real.log (projectiveCycleDenom z)) y‖ ≤ 7 / α := by
  have hH0 : 0 < projectiveCycleDenom y := lt_of_lt_of_le (by positivity) hH
  have HD := (cycle_terminal_coefficient_bounds hm hw).2
  have HN := clm_norm_le_card_mul_basis_bound (fderiv ℝ projectiveCycleDenom y)
    (show 0 ≤ 6 * α by positivity) (fun j => by
      rw [Real.norm_eq_abs, projectiveCycleDenom_fderiv]
      exact HD j)
  have HN' : ‖fderiv ℝ projectiveCycleDenom y‖ ≤ 24 * α := by norm_num at HN; linarith only [HN]
  have hd := ((contDiff_projectiveCycleDenom 1).differentiable (by norm_num) y).hasFDerivAt
  rw [(hd.log hH0.ne').fderiv, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hH0]
  calc
    _ ≤ (projectiveCycleDenom y)⁻¹ * (24 * α) := mul_le_mul_of_nonneg_left HN' (inv_nonneg.mpr hH0.le)
    _ = 24 * α / projectiveCycleDenom y := by ring
    _ ≤ 7 / α := by
      apply (div_le_div_iff₀ hH0 hα).mpr
      nlinarith only [hH, sq_nonneg α]

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
open Filter
open scoped Topology

private theorem BianchiIX.coreTailState_eventuallyEq_reconstruction {h : ℝ} {Y : ExitTailState}
    (hR : 1 < Y 0) (HV : coreTailValid h Y) (hm : coreTailState h Y 0 < 1) :
    coreTailState h =ᶠ[𝓝 Y] (fun Z => fromExitTailState h (toExitTailState (coreTailState h Z))) := by
  have HR := coreTail_regular_of_valid hR HV
  have Hm := (continuousAt_pi.mp HR.2.1.continuousAt 0).eventually (isOpen_Iio.mem_nhds hm)
  filter_upwards [HR.2.2, Hm] with Z hZ hmZ
  have H := fromExitTailState_toExitTailState hmZ
  rw [coreTailState_active hZ] at H
  exact H.symm

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.coreTailState_fderiv_bound_of_radial {h B : ℝ} {Y : ExitTailState}
    (hR : 1 < Y 0) (HV : coreTailValid h Y) (hm : coreTailState h Y 0 < 1)
    (hr : 7 / 4 ≤ coreRadius (coreTailState h Y 0) (coreTailState h Y 2)) (hh : |h| ≤ 1)
    (HF : ContDiffAt ℝ 2 (fun Z => toExitTailState (coreTailState h Z)) Y)
    (HB : ‖fderiv ℝ (fun Z => toExitTailState (coreTailState h Z)) Y‖ ≤ B) :
    ‖fderiv ℝ (coreTailState h) Y‖ ≤ 2 * B := by
  have HE := coreTailState_eventuallyEq_reconstruction hR HV hm
  have HG := fromExitTailState_fderiv_bound (Y := toExitTailState (coreTailState h Y)) (h := h) hr hh
  rw [HE.fderiv_eq]
  change ‖fderiv ℝ (fromExitTailState h ∘ fun Z => toExitTailState (coreTailState h Z)) Y‖ ≤ _
  rw [fderiv_comp Y (HG.1.differentiableAt (by norm_num)) (HF.differentiableAt (by norm_num))]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul HG.2 HB (norm_nonneg _) (by norm_num))

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_terminal_tail_geometry_uniform {η₀ : ℝ} (hη₀ : 0 < η₀ ∧ η₀ ≤ 1 / 100)
    {J : ℕ} (hJ : 1 ≤ J) :
    ∃ A ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ η α b u w : ℝ,
      η₀ ≤ η → η ≤ 1 / 100 → (0 < α ∧ α ≤ 1) →
      0 < b → b ≤ ε * α ^ (2 * J) → |u| + |w| ≤ b →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      let y := coreTailState h Y
      coreTailValid h Y ∧ y 0 < 1 ∧
        |coreRadius (y 0) (y 2) - (2 + 2 * α)| ≤ A * b ∧
        |y 1| + |y 3| ≤ A * b ∧ A * b ≤ α / 10000 ∧
        (0 ≤ y 2 ∧ y 2 ≤ α / 100) ∧ 39 / 10 * α ^ 2 ≤ projectiveCycleDenom y := by
  obtain ⟨A, hA, ε, hε, HE⟩ := exists_terminal_axisCycle_regular hη₀ hJ
  refine ⟨A, hA, ε, hε, ?_⟩
  intro η α b u w hηlo hηhi hα hb hsmall hsum Y h y
  have hη : 0 < η := hη₀.1.trans_le hηlo
  obtain ⟨HV₀, HB, HF, _⟩ := HE α b u w hα hb hsmall hsum
  have hh1 : h < 1 := by
    have H := mul_le_mul_of_nonneg_left (pow_le_one₀ hα.1.le hα.2 (n := J)) hη.le
    dsimp only [h]
    nlinarith only [H, hηhi]
  obtain ⟨HV, htime⟩ := coreTailValid_of_height_le HV₀
    (mul_le_mul_of_nonneg_right hηlo (pow_nonneg hα.1.le J)) hh1
  change coreTailValid h Y at HV
  have H := HF (coreTailTime h Y) ⟨HV.1.1.1.le, htime⟩
  have HB' : A * b ≤ α / 10000 := HB.trans (div_le_div_of_nonneg_right
    ((pow_le_pow_of_le_one hα.1.le hα.2 (by omega : 1 ≤ 2 * J)).trans_eq (pow_one α)) (by norm_num))
  have hv : 0 ≤ y 2 ∧ y 2 ≤ α / 100 := by
    change 0 ≤ coreTailState h Y 2 ∧ coreTailState h Y 2 ≤ _
    rw [coreTailState_active HV]
    refine ⟨mul_nonneg hη.le (pow_nonneg hα.1.le J), ?_⟩
    have hp := (pow_le_pow_of_le_one hα.1.le hα.2 hJ).trans_eq (pow_one α)
    change η * α ^ J ≤ _
    nlinarith only [mul_le_mul_of_nonneg_left hp hη.le, mul_le_mul_of_nonneg_right hηhi hα.1.le]
  refine ⟨HV, H.1, H.2.1, H.2.2.1, HB', hv, ?_⟩
  have HH : 39 / 10 * α ^ 2 + 2 / 5 * (y 2) ^ 2 < projectiveCycleDenom y := H.2.2.2.1
  nlinarith only [HH, sq_nonneg (y 2)]

end
end


/-- The actual fixed-height tail followed by the cyclic chart has the alpha^-2 derivative bound. -/
theorem solution {η₀ : ℝ} (hη₀ : 0 < η₀ ∧ η₀ ≤ 1 / 100)
    {J : ℕ} (hJ : 1 ≤ J) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ η α b u w : ℝ,
      η₀ ≤ η → η ≤ 1 / 100 → (0 < α ∧ α ≤ 1) →
      0 < b → b ≤ ε * α ^ (2 * J) → |u| + |w| ≤ b →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      coreTailValid h Y ∧ ContDiffAt ℝ 2 (terminalCyclicInput h) Y ∧
        ‖fderiv ℝ (terminalCyclicInput h) Y‖ ≤ C / α ^ 2 ∧
        ‖fderiv ℝ (fun Z => Real.log (projectiveCycleDenom (coreTailState h Z))) Y‖ ≤ C / α := by
  obtain ⟨A, _, εg, hεg, HG⟩ := exists_terminal_tail_geometry_uniform hη₀ hJ
  obtain ⟨B, hB, εd, hεd, HD⟩ := exists_terminal_exitReturn_two_bounds_uniform
    ⟨hη₀.1, by linarith only [hη₀.2]⟩ hJ
  have hB0 : 0 < B := lt_of_lt_of_le (by norm_num) hB
  refine ⟨48 * B, by linarith only [hB], min εg εd, lt_min hεg hεd, ?_⟩
  intro η α b u w hηlo hηhi hα hb hsmall hsum Y h
  have hα0 : 0 < α := hα.1
  have hsmallg := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_left εg εd) (pow_nonneg hα.1.le (2 * J)))
  have hsmalld : b ≤ εd * α ^ J := hsmall.trans
    ((mul_le_mul_of_nonneg_right (min_le_right εg εd) (pow_nonneg hα.1.le (2 * J))).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hα.1.le hα.2 (by omega)) hεd.le))
  obtain ⟨HV, HM, HR, HW, HB, HVbounds, HH⟩ := HG η α b u w hηlo hηhi hα hb hsmallg hsum
  change coreTailValid h Y at HV
  have Hder := HD η α b u w hηlo (by linarith only [hηhi]) hα hb hsmalld hsum
  let y := coreTailState h Y
  have hr : 7 / 4 ≤ coreRadius (y 0) (y 2) := by linarith only [(abs_le.mp HR).1, HB, hα.1]
  have hh : |h| ≤ 1 := by
    rw [← coreTailState_active HV, abs_of_nonneg HVbounds.1]
    linarith only [HVbounds.2, hα.2]
  have hR : 1 < Y 0 := by change 1 < 2 + 2 * α; linarith only [hα.1]
  have Htail := coreTailState_fderiv_bound_of_radial hR HV HM hr hh Hder.2.1 Hder.2.2.1
  have Hreg := (coreTail_regular_of_valid hR HV).2.1
  have hH : 0 < projectiveCycleDenom y := lt_of_lt_of_le (by positivity) HH
  have HGc := contDiffAt_projectiveCycle 2 hH.ne'
  have Hgap := exitTailGap_terminal_offset hα HB HR HVbounds
  rw [exitTailGap_of_coreRadius HM] at Hgap
  have hm : |y 0 + 1| ≤ 3 * α := abs_le.mpr (by constructor <;> linarith only [Hgap.1, Hgap.2, hα.1])
  have hw : |y 1| + |y 2| + |y 3| ≤ 3 * α := by
    rw [abs_of_nonneg HVbounds.1]
    linarith only [HW, HB, HVbounds.2, hα.1]
  have Hcycle : ‖fderiv ℝ projectiveCycle y‖ ≤ 24 / α ^ 2 :=
    fderiv_norm_le_of_coordinate_bounds (by positivity) (HGc.differentiableAt (by norm_num))
      (fun i => (projectiveCycle_terminal_operator_bounds hα.1 HH hm hw i).1)
  have Hlog := projectiveCycle_log_denom_derivative_bound hα.1 HH hm hw
  have Hlogreg : ContDiffAt ℝ 2 (fun z => Real.log (projectiveCycleDenom z)) y :=
    (contDiff_projectiveCycleDenom 2).contDiffAt.log hH.ne'
  refine ⟨HV, ContDiffAt.comp (g := projectiveCycle) (f := coreTailState h) Y HGc Hreg, ?_, ?_⟩
  · change ‖fderiv ℝ (projectiveCycle ∘ coreTailState h) Y‖ ≤ _
    rw [fderiv_comp Y (HGc.differentiableAt (by norm_num)) (Hreg.differentiableAt (by norm_num))]
    exact ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul Hcycle Htail (norm_nonneg _) (by positivity))).trans_eq (by ring)
  · change ‖fderiv ℝ ((fun z => Real.log (projectiveCycleDenom z)) ∘ coreTailState h) Y‖ ≤ _
    rw [fderiv_comp Y (Hlogreg.differentiableAt (by norm_num)) (Hreg.differentiableAt (by norm_num))]
    apply ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul Hlog Htail (norm_nonneg _) (by positivity))).trans
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hα.1.le
    nlinarith only [hB]
