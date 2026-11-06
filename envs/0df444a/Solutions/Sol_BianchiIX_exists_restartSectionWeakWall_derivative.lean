-- Prove2me | solution 1 for BianchiIX.exists_restartSectionWeakWall_derivative
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:40:12.138846+00:00
-- url     : https://prove2.me/submissions/3efbc132-ac79-49b0-9b6c-5d9670a1c587

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_SectionRestartData
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_RadialTransportData
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Theorems.Thm_BianchiIX_contDiffAt_intervalIntegral_of_contDiffAt
import Theorems.Thm_BianchiIX_contDiffAt_intervalIntegral_two
import Theorems.Thm_BianchiIX_contDiffAt_normalizedMaxCurve_nat
import Theorems.Thm_BianchiIX_hasDerivAt_normalized_components
import Theorems.Thm_BianchiIX_hasFDerivAt_intervalIntegral_of_contDiffAt
import Theorems.Thm_BianchiIX_homogeneous_solution_eq_exp_integral_Icc
import Theorems.Thm_BianchiIX_le_exp_of_clock_deriv_le
import Theorems.Thm_BianchiIX_norm_le_exp_of_norm_deriv_clock
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward_of_constraint
import Theorems.Thm_BianchiIX_normalizedMaxCurve_regular
import Theorems.Thm_BianchiIX_normalizedMaxCurve_wall_sign
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_normalized_constraint_constant
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
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

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
open Filter
open scoped Topology
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

private theorem BianchiIX.fderiv2_comp_apply {f : E → F} {g : F → G} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g (f x)) (v w : E) :
    fderiv ℝ (fderiv ℝ (g ∘ f)) x v w =
      fderiv ℝ g (f x) (fderiv ℝ (fderiv ℝ f) x v w) +
        fderiv ℝ (fderiv ℝ g) (f x) (fderiv ℝ f x v) (fderiv ℝ f x w) := by
  have hf' := (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num)
  have hg' := (hg.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num)
  have hcomp := ((hg.comp x hf).fderiv_right
    (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num)
  have heq : (fun y => fderiv ℝ (g ∘ f) y w) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ g (f y) (fderiv ℝ f y w)) := by
    filter_upwards [hf.eventually (by norm_num), hf.continuousAt.eventually (hg.eventually (by norm_num))]
      with y hfy hgy
    rw [fderiv_comp y (hgy.differentiableAt (by norm_num)) (hfy.differentiableAt (by norm_num))]
    rfl
  have Hleft := hcomp.hasFDerivAt.clm_apply (hasFDerivAt_const w x)
  have Hright := (hg'.hasFDerivAt.comp x (hf.differentiableAt (by norm_num)).hasFDerivAt).clm_apply
    (hf'.hasFDerivAt.clm_apply (hasFDerivAt_const w x))
  have H := congrArg (fun L : E →L[ℝ] G => L v) (Hleft.unique (Hright.congr_of_eventuallyEq heq))
  simpa using H

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

private theorem BianchiIX.fderiv2_clm_comp_apply {f : E → F} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (L : F →L[ℝ] G) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => L (f y))) x v w =
      L (fderiv ℝ (fderiv ℝ f) x v w) := by
  have H := fderiv2_comp_apply hf L.contDiff.contDiffAt v w
  have hL : fderiv ℝ (L : F → G) = fun _ => L := funext (fun _ => L.fderiv)
  simpa only [hL, fderiv_const_apply, zero_apply, add_zero, Function.comp_def] using H

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem BianchiIX.fderiv_parameterSlice_apply {Φ : E × ℝ → F} {x : E} {t : ℝ}
    (H : DifferentiableAt ℝ Φ (x, t)) (v : E) :
    fderiv ℝ (fun y => Φ (y, t)) x v = fderiv ℝ Φ (x, t) (v, 0) := by
  have HD := H.hasFDerivAt.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x t)
  change HasFDerivAt (fun y => Φ (y, t)) _ x at HD
  rw [HD.fderiv]
  rfl

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem BianchiIX.hasDerivAt_parametric_first_variation {Φ : E × ℝ → F} {f : ℝ × F → F} {x : E} {t : ℝ}
    (hΦ : ContDiffAt ℝ 2 Φ (x, t)) (hf : DifferentiableAt ℝ f (t, Φ (x, t)))
    (hode : (fun p => fderiv ℝ Φ p (0, 1)) =ᶠ[𝓝 (x, t)] (fun p => f (p.2, Φ p))) (v : E) :
    HasDerivAt (fun s => fderiv ℝ Φ (x, s) (v, 0))
      (fderiv ℝ (fun z => f (t, z)) (Φ (x, t)) (fderiv ℝ Φ (x, t) (v, 0))) t := by
  have hD := (hΦ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hleft := hD.hasFDerivAt.clm_apply (hasFDerivAt_const (0, 1) (x, t))
  have hright := hf.hasFDerivAt.comp (x, t)
    (hasFDerivAt_snd.prodMk (hΦ.differentiableAt (by norm_num)).hasFDerivAt)
  have heq := congrArg (fun L : (E × ℝ) →L[ℝ] F => L (v, 0))
    ((hleft.congr_of_eventuallyEq hode.symm).unique hright)
  have hslice := hf.hasFDerivAt.comp (Φ (x, t))
    ((hasFDerivAt_const t (Φ (x, t))).prodMk (hasFDerivAt_id (Φ (x, t))))
  change HasFDerivAt (fun z => f (t, z)) _ (Φ (x, t)) at hslice
  have hpath : HasDerivAt (fun s : ℝ => (x, s)) (0, 1) t :=
    (hasDerivAt_const t x).prodMk (hasDerivAt_id t)
  have H := hasDerivAt_fderiv_apply_const hD hpath (v, 0)
  apply H.congr_deriv
  rw [(hΦ.isSymmSndFDerivAt (by norm_num)).eq (0, 1) (v, 0), hslice.fderiv]
  simpa using heq

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restart_negative_branch_root {x : NormalizedState}
    (hc : stateConstraint x = 1) (hp : x 0 < 0) :
    -x 0 = Real.sqrt (1 - x 1 ^ 2 - curvature (x 2) (x 3) (x 4)) := by
  have hr : 1 - x 1 ^ 2 - curvature (x 2) (x 3) (x 4) = x 0 ^ 2 := by
    dsimp only [stateConstraint, constraint, shearSq] at hc
    linarith only [hc]
  rw [hr, Real.sqrt_sq_eq_abs, abs_of_neg hp]

end
end

section
noncomputable section
open BianchiIX
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

private theorem BianchiIX.composition_second_derivative_bounds {f : E → F} {g : F → G} {x : E} {A B K : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g (f x))
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hf1 : ‖fderiv ℝ f x‖ ≤ K) (hf2 : ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ K)
    (hg1 : ‖fderiv ℝ g (f x)‖ ≤ A) (hg2 : ‖fderiv ℝ (fderiv ℝ g) (f x)‖ ≤ B) :
    ‖fderiv ℝ (g ∘ f) x‖ ≤ A * K ∧
      ‖fderiv ℝ (fderiv ℝ (g ∘ f)) x‖ ≤ A * K + B * K ^ 2 := by
  have hf1' (v : E) : ‖fderiv ℝ f x v‖ ≤ K * ‖v‖ :=
    ((fderiv ℝ f x).le_opNorm v).trans (mul_le_mul_of_nonneg_right hf1 (norm_nonneg v))
  have hf2' (v w : E) : ‖fderiv ℝ (fderiv ℝ f) x v w‖ ≤ K * ‖v‖ * ‖w‖ :=
    (((fderiv ℝ (fderiv ℝ f) x) v).le_opNorm w).trans
      (mul_le_mul_of_nonneg_right (((fderiv ℝ (fderiv ℝ f) x).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right hf2 (norm_nonneg v))) (norm_nonneg w))
  constructor
  · rw [fderiv_comp x (hg.differentiableAt (by norm_num)) (hf.differentiableAt (by norm_num))]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul hg1 hf1 (norm_nonneg _) hA)
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro w
    rw [fderiv2_comp_apply hf hg]
    have H1 := ((fderiv ℝ g (f x)).le_opNorm (fderiv ℝ (fderiv ℝ f) x v w)).trans
      (mul_le_mul hg1 (hf2' v w) (norm_nonneg _) hA)
    let L := fderiv ℝ (fderiv ℝ g) (f x)
    have H2 := ((L (fderiv ℝ f x v)).le_opNorm (fderiv ℝ f x w)).trans
      (mul_le_mul_of_nonneg_right (L.le_opNorm _) (norm_nonneg _))
    have H3 := mul_le_mul (mul_le_mul hg2 (hf1' v) (norm_nonneg _) hB)
      (hf1' w) (norm_nonneg _) (by positivity : 0 ≤ B * (K * ‖v‖))
    have Hsum := norm_add_le (fderiv ℝ g (f x) (fderiv ℝ (fderiv ℝ f) x v w))
      (L (fderiv ℝ f x v) (fderiv ℝ f x w))
    dsimp only [L] at H2 Hsum
    nlinarith only [H1, H2, H3, Hsum]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiff_restartRadicand (k : WithTop ℕ∞) : ContDiff ℝ k restartRadicand := by
  unfold restartRadicand curvature
  fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_restartCompactRoot {x : RestartState} (hx : 0 < restartRadicand x)
    (k : WithTop ℕ∞) : ContDiffAt ℝ k restartCompactRoot x :=
  (contDiff_restartRadicand k).contDiffAt.sqrt hx.ne'

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_restartCompactField {x : RestartState} (hx : 0 < restartRadicand x)
    (k : WithTop ℕ∞) : ContDiffAt ℝ k restartCompactField x := by
  have hr := contDiffAt_restartCompactRoot hx k
  rw [contDiffAt_pi]
  intro i
  fin_cases i <;> dsimp [restartCompactField, restartCompactWeakRate, shearMinus, curvature] <;> fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiff_restartExpCoordinates (k : WithTop ℕ∞) : ContDiff ℝ k restartExpCoordinates := by
  rw [contDiff_pi]
  intro i
  fin_cases i <;> dsimp [restartExpCoordinates] <;> fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_restartMixedField {y : RestartState}
    (hy : 0 < restartRadicand (restartExpCoordinates y)) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k restartMixedField y :=
  (contDiffAt_restartCompactField hy k).comp y (contDiff_restartExpCoordinates k).contDiffAt

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasFDerivAt_restartCompactField_zero : HasFDerivAt (𝕜 := ℝ) restartCompactField 0 0 := by
  have hp (i : Fin 4) := hasFDerivAt_apply (𝕜 := ℝ) i (0 : RestartState)
  have hQ : HasFDerivAt (𝕜 := ℝ) (fun x : RestartState => curvature (x 0) (x 2) (x 3)) 0 0 := by
    have H := (((hp 0).pow 2).add ((hp 2).pow 2) |>.add ((hp 3).pow 2)).sub
      ((((hp 0).mul (hp 2)).add ((hp 2).mul (hp 3)) |>.add ((hp 3).mul (hp 0))).const_mul 2)
    convert! H using 1
    simp
  have hR : HasFDerivAt (𝕜 := ℝ) restartRadicand 0 0 := by
    convert! (((hp 1).pow 2).const_sub 1).sub hQ using 1
    simp
  have hr : HasFDerivAt (𝕜 := ℝ) restartCompactRoot 0 0 := by
    convert! hR.sqrt (by norm_num [restartRadicand, curvature] : restartRadicand 0 ≠ 0) using 1
    simp
  have hH : HasFDerivAt (𝕜 := ℝ) (fun x : RestartState => -(x 2) ^ 2 + (x 3) ^ 2 + x 0 * x 2 - x 0 * x 3) 0 0 := by
    convert! ((((hp 2).pow 2).neg.add ((hp 3).pow 2)).add ((hp 0).mul (hp 2))).sub
      ((hp 0).mul (hp 3)) using 1
    simp
  have hg (ε : ℝ) := ((hQ.sub_const 1).add hr).add ((hp 1).const_mul (ε * Real.sqrt 3))
  apply hasFDerivAt_pi'.mpr
  intro i
  fin_cases i
  · convert! (hQ.sub_const 1).sub (hr.const_mul 2) using 1
    simp
  · convert! (hQ.mul (hp 1)).add (hH.const_mul (Real.sqrt 3)) using 1
    simp [curvature]
  · convert! (hp 2).mul (hg 1) using 1
    simp [curvature, restartCompactRoot, restartRadicand]
  · convert! (hp 3).mul (hg (-1)) using 1
    simp [curvature, restartCompactRoot, restartRadicand]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartCompactField_fderiv_zero : fderiv ℝ restartCompactField 0 = 0 :=
  hasFDerivAt_restartCompactField_zero.fderiv

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartMixedField_coordinates {x : NormalizedState}
    (hc : stateConstraint x = 1) (hp : x 0 < 0) (hn : 0 < x 2) :
    restartMixedField (restartMixedCoordinates x) =
      ![rateOne (x 0) (x 1), shearMinus (x 1) (x 2) (x 3) (x 4),
        rateTwo (x 0) (x 1) * x 3, rateThree (x 0) (x 1) * x 4] := by
  have hroot := restart_negative_branch_root hc hp
  have hq : curvature (x 2) (x 3) (x 4) = 1 - shearSq (x 0) (x 1) := by
    dsimp only [stateConstraint, constraint] at hc
    linarith only [hc]
  ext i
  fin_cases i <;>
    simp [restartMixedField, restartMixedCoordinates, restartExpCoordinates, restartCompactField,
      restartCompactWeakRate, restartCompactRoot, restartRadicand, Real.exp_log hn] <;>
    rw [← hroot, hq] <;> dsimp only [rateOne, rateTwo, rateThree] <;> ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_restartMixedCoordinates {x : ℝ → NormalizedState} {t : ℝ}
    (hx : HasDerivAt x (normalizedField (x t)) t) (hc : stateConstraint (x t) = 1)
    (hp : x t 0 < 0) (hn : 0 < x t 2) :
    HasDerivAt (fun r => restartMixedCoordinates (x r))
      (restartMixedField (restartMixedCoordinates (x t))) t := by
  rw [restartMixedField_coordinates hc hp hn]
  obtain ⟨_, hs, hN, ha, hb⟩ := hasDerivAt_normalized_components hx
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · change HasDerivAt (fun r => Real.log (x r 2)) (rateOne (x t 0) (x t 1)) t
    convert! hN.log hn.ne' using 1
    simp only [mul_div_cancel_right₀ _ hn.ne']
  · exact hs
  · exact ha
  · exact hb

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartCompact_box_bounds {x : RestartState} (hx : ‖x‖ ≤ 1 / 16) :
    |curvature (x 0) (x 2) (x 3)| ≤ 9 / 256 ∧
      246 / 256 ≤ restartRadicand x ∧ restartRadicand x ≤ 265 / 256 ∧
      15 / 16 ≤ restartCompactRoot x ∧ restartCompactRoot x ≤ 17 / 16 ∧
      -4 < restartCompactField x 0 ∧ restartCompactField x 0 < -2 := by
  have hc (i : Fin 4) : |x i| ≤ 1 / 16 := (norm_le_pi_norm x i).trans hx
  have hs (i : Fin 4) : (x i) ^ 2 ≤ 1 / 256 := by
    obtain ⟨hl, hu⟩ := abs_le.mp (hc i)
    nlinarith only [hl, hu]
  have hm (i j : Fin 4) : |x i * x j| ≤ 1 / 256 := by
    rw [abs_mul]
    calc
      _ ≤ (1 / 16 : ℝ) * (1 / 16) := mul_le_mul (hc i) (hc j) (abs_nonneg _) (by norm_num)
      _ = _ := by norm_num
  have hQ : |curvature (x 0) (x 2) (x 3)| ≤ 9 / 256 := by
    obtain ⟨h02l, h02u⟩ := abs_le.mp (hm 0 2)
    obtain ⟨h23l, h23u⟩ := abs_le.mp (hm 2 3)
    obtain ⟨h30l, h30u⟩ := abs_le.mp (hm 3 0)
    apply abs_le.mpr
    dsimp only [curvature]
    constructor
    · nlinarith only [sq_nonneg (x 0), sq_nonneg (x 2), sq_nonneg (x 3), h02u, h23u, h30u]
    · nlinarith only [hs 0, hs 2, hs 3, h02l, h23l, h30l]
  have hRl : 246 / 256 ≤ restartRadicand x := by
    dsimp only [restartRadicand]
    linarith only [hs 1, (abs_le.mp hQ).2]
  have hRu : restartRadicand x ≤ 265 / 256 := by
    dsimp only [restartRadicand]
    linarith only [sq_nonneg (x 1), (abs_le.mp hQ).1]
  have hr0 : 0 ≤ restartCompactRoot x := Real.sqrt_nonneg _
  have hr2 : restartCompactRoot x ^ 2 = restartRadicand x := Real.sq_sqrt (by linarith only [hRl])
  have hrl : 15 / 16 ≤ restartCompactRoot x := by nlinarith only [hr0, hr2, hRl]
  have hru : restartCompactRoot x ≤ 17 / 16 := by nlinarith only [hr0, hr2, hRu]
  refine ⟨hQ, hRl, hRu, hrl, hru, ?_, ?_⟩
  · change -4 < curvature (x 0) (x 2) (x 3) - 1 - 2 * restartCompactRoot x
    linarith only [(abs_le.mp hQ).1, hru]
  · change curvature (x 0) (x 2) (x 3) - 1 - 2 * restartCompactRoot x < -2
    linarith only [(abs_le.mp hQ).2, hrl]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartCompact_derivative_bounds :
    ∃ C ≥ (1 : ℝ), ∀ x : RestartState, ‖x‖ ≤ 1 / 16 →
      ‖fderiv ℝ restartCompactField x‖ ≤ C * ‖x‖ ∧
        ‖fderiv ℝ (fderiv ℝ restartCompactField) x‖ ≤ C := by
  let S := Metric.closedBall (0 : RestartState) (1 / 16)
  have hreg (x : RestartState) (hx : x ∈ S) : ContDiffAt ℝ 3 restartCompactField x := by
    have H := (restartCompact_box_bounds (by simpa [S] using hx)).2.1
    exact contDiffAt_restartCompactField (by linarith only [H]) 3
  have hq : ContinuousOn (fun x => ‖fderiv ℝ (fderiv ℝ restartCompactField) x‖) S := by
    intro x hx
    exact (((hreg x hx).fderiv_right (m := 2) (by norm_num)).fderiv_right
      (m := 1) (by norm_num)).continuousAt.norm.continuousWithinAt
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : RestartState) (1 / 16)).exists_bound_of_continuousOn hq
  let C := max B 1
  have hbound (x : RestartState) (hx : x ∈ S) :
      ‖fderiv ℝ (fderiv ℝ restartCompactField) x‖ ≤ C := by
    exact (le_abs_self _).trans ((hB x hx).trans (le_max_left B 1))
  have hdiff (x : RestartState) (hx : x ∈ S) : DifferentiableAt ℝ (fderiv ℝ restartCompactField) x :=
    ((hreg x hx).fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
  refine ⟨C, le_max_right _ _, ?_⟩
  intro x hx
  have hxS : x ∈ S := by simpa [S] using hx
  have hzS : (0 : RestartState) ∈ S := by simp [S]
  have H := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hbound
    (convex_closedBall (0 : RestartState) (1 / 16)) hzS hxS
  exact ⟨by simpa only [restartCompactField_fderiv_zero, sub_zero] using H, hbound x hxS⟩

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasFDerivAt_restartExpCoordinates (y : RestartState) :
    HasFDerivAt restartExpCoordinates (restartExpDifferential (Real.exp (y 0))) y := by
  apply hasFDerivAt_pi'.mpr
  intro i
  fin_cases i
  · exact (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 4) y).exp
  · exact hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 4) y
  · exact hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 4) y
  · exact hasFDerivAt_apply (𝕜 := ℝ) (3 : Fin 4) y

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartExpCoordinates_fderiv (y v : RestartState) :
    fderiv ℝ restartExpCoordinates y v = ![Real.exp (y 0) * v 0, v 1, v 2, v 3] := by
  rw [(hasFDerivAt_restartExpCoordinates y).fderiv]
  ext i
  fin_cases i <;> rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartExpCoordinates_fderiv2 (y v w : RestartState) :
    fderiv ℝ (fderiv ℝ restartExpCoordinates) y v w =
      ![Real.exp (y 0) * v 0 * w 0, 0, 0, 0] := by
  have hp (i : Fin 4) : fderiv ℝ (fun z : RestartState => z i) = fun _ => ContinuousLinearMap.proj i :=
    funext (fun z => (hasFDerivAt_apply (𝕜 := ℝ) i z).fderiv)
  have he : fderiv ℝ (fun z : RestartState => Real.exp (z 0)) =
      fun z => Real.exp (z 0) • (ContinuousLinearMap.proj 0 : RestartState →L[ℝ] ℝ) :=
    funext (fun z => (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 4) z).exp.fderiv)
  have he2 : fderiv ℝ (fderiv ℝ (fun z : RestartState => Real.exp (z 0))) y v w =
      Real.exp (y 0) * v 0 * w 0 := by
    rw [he, (((hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 4) y).exp).smul_const
      (ContinuousLinearMap.proj 0 : RestartState →L[ℝ] ℝ)).fderiv]
    rfl
  have H (i : Fin 4) := fderiv2_clm_comp_apply (x := y) (contDiff_restartExpCoordinates 2).contDiffAt
    (ContinuousLinearMap.proj i) v w
  ext i
  fin_cases i
  · have H0 := H 0
    change fderiv ℝ (fderiv ℝ (fun z : RestartState => Real.exp (z 0))) y v w = _ at H0
    exact (he2.symm.trans H0).symm
  · have H1 := H 1
    change fderiv ℝ (fderiv ℝ (fun z : RestartState => z 1)) y v w = _ at H1
    rw [hp, fderiv_const_apply] at H1
    exact H1.symm
  · have H2 := H 2
    change fderiv ℝ (fderiv ℝ (fun z : RestartState => z 2)) y v w = _ at H2
    rw [hp, fderiv_const_apply] at H2
    exact H2.symm
  · have H3 := H 3
    change fderiv ℝ (fderiv ℝ (fun z : RestartState => z 3)) y v w = _ at H3
    rw [hp, fderiv_const_apply] at H3
    exact H3.symm

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartExpCoordinates_derivative_bounds {y : RestartState} (hy : Real.exp (y 0) ≤ 1) :
    ‖fderiv ℝ restartExpCoordinates y‖ ≤ 1 ∧
      ‖fderiv ℝ (fderiv ℝ restartExpCoordinates) y‖ ≤ 1 := by
  have hv (v : RestartState) (i : Fin 4) : |v i| ≤ ‖v‖ := norm_le_pi_norm v i
  have hn : 0 ≤ Real.exp (y 0) := (Real.exp_pos _).le
  have hfirst (v : RestartState) : |Real.exp (y 0) * v 0| ≤ ‖v‖ := by
    rw [abs_mul, abs_of_nonneg hn]
    exact (mul_le_mul_of_nonneg_left (hv v 0) hn).trans (mul_le_of_le_one_left (norm_nonneg v) hy)
  constructor
  · apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro v
    rw [one_mul, restartExpCoordinates_fderiv]
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
    intro i
    fin_cases i
    · exact hfirst v
    · exact hv v 1
    · exact hv v 2
    · exact hv v 3
  · apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro v
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro w
    rw [one_mul, restartExpCoordinates_fderiv2]
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg v) (norm_nonneg w))).mpr
    intro i
    fin_cases i
    · change |Real.exp (y 0) * v 0 * w 0| ≤ _
      rw [abs_mul]
      exact mul_le_mul (hfirst v) (hv w 0) (abs_nonneg _) (norm_nonneg v)
    all_goals simpa using mul_nonneg (norm_nonneg v) (norm_nonneg w)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exists_restartMixed_derivative_bounds :
    ∃ C ≥ (1 : ℝ), ∀ y : RestartState, ‖restartExpCoordinates y‖ ≤ 1 / 16 →
      ‖fderiv ℝ restartMixedField y‖ ≤ C * ‖restartExpCoordinates y‖ ∧
        ‖fderiv ℝ (fderiv ℝ restartMixedField) y‖ ≤ C := by
  obtain ⟨B, hB, HB⟩ := exists_restartCompact_derivative_bounds
  have hB0 : 0 ≤ B := by linarith only [hB]
  refine ⟨2 * B, by linarith only [hB], ?_⟩
  intro y hy
  have hn : Real.exp (y 0) ≤ 1 := by
    have H : |Real.exp (y 0)| ≤ 1 / 16 := (norm_le_pi_norm (restartExpCoordinates y) 0).trans hy
    rw [abs_of_pos (Real.exp_pos _)] at H
    linarith only [H]
  have hr : 0 < restartRadicand (restartExpCoordinates y) := by
    have H := (restartCompact_box_bounds hy).2.1
    linarith only [H]
  have H := composition_second_derivative_bounds (contDiff_restartExpCoordinates 2).contDiffAt
    (contDiffAt_restartCompactField hr 2) (mul_nonneg hB0 (norm_nonneg _)) hB0 (by norm_num : (0 : ℝ) ≤ 1)
    (restartExpCoordinates_derivative_bounds hn).1 (restartExpCoordinates_derivative_bounds hn).2
    (HB _ hy).1 (HB _ hy).2
  change ‖fderiv ℝ restartMixedField y‖ ≤ B * ‖restartExpCoordinates y‖ * 1 ∧
    ‖fderiv ℝ (fderiv ℝ restartMixedField) y‖ ≤ B * ‖restartExpCoordinates y‖ * 1 + B * 1 ^ 2 at H
  constructor
  · nlinarith only [H.1, mul_nonneg hB0 (norm_nonneg (restartExpCoordinates y))]
  · nlinarith only [H.2, mul_le_mul_of_nonneg_left hy hB0, hB0]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_restartCompactWeakRates {x : RestartState} (hx : 0 < restartRadicand x)
    (k : WithTop ℕ∞) : ContDiffAt ℝ k restartCompactWeakRates x := by
  have hr := contDiffAt_restartCompactRoot hx k
  rw [contDiffAt_pi]
  intro i
  fin_cases i <;> dsimp [restartCompactWeakRates, restartCompactWeakRate, curvature] <;> fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartCompactWeakRates_zero : restartCompactWeakRates 0 = 0 := by
  ext i
  fin_cases i <;> norm_num [restartCompactWeakRates, restartCompactWeakRate,
    restartCompactRoot, restartRadicand, curvature]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exists_restartCompactWeakRates_bounds :
    ∃ C ≥ (1 : ℝ), ∀ x : RestartState, ‖x‖ ≤ 1 / 16 →
      ‖restartCompactWeakRates x‖ ≤ C * ‖x‖ ∧
        ‖fderiv ℝ restartCompactWeakRates x‖ ≤ C ∧
        ‖fderiv ℝ (fderiv ℝ restartCompactWeakRates) x‖ ≤ C := by
  let S := Metric.closedBall (0 : RestartState) (1 / 16)
  have hreg (x : RestartState) (hx : x ∈ S) : ContDiffAt ℝ 3 restartCompactWeakRates x := by
    have H := (restartCompact_box_bounds (by simpa [S] using hx)).2.1
    exact contDiffAt_restartCompactWeakRates (by linarith only [H]) 3
  let q := fun x => ‖fderiv ℝ restartCompactWeakRates x‖ + ‖fderiv ℝ (fderiv ℝ restartCompactWeakRates) x‖
  have hq : ContinuousOn q S := by
    intro x hx
    have HD := (hreg x hx).fderiv_right (m := 2) (by norm_num)
    exact (HD.continuousAt.norm.add
      (HD.fderiv_right (m := 1) (by norm_num)).continuousAt.norm).continuousWithinAt
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : RestartState) (1 / 16)).exists_bound_of_continuousOn hq
  let C := max B 1
  have hbound (x : RestartState) (hx : x ∈ S) :
      ‖fderiv ℝ restartCompactWeakRates x‖ ≤ C ∧
        ‖fderiv ℝ (fderiv ℝ restartCompactWeakRates) x‖ ≤ C := by
    have H : q x ≤ C := (le_abs_self _).trans ((hB x hx).trans (le_max_left B 1))
    dsimp only [q] at H
    exact ⟨by linarith only [H, norm_nonneg (fderiv ℝ (fderiv ℝ restartCompactWeakRates) x)],
      by linarith only [H, norm_nonneg (fderiv ℝ restartCompactWeakRates x)]⟩
  refine ⟨C, le_max_right _ _, ?_⟩
  intro x hx
  have hxS : x ∈ S := by simpa [S] using hx
  have hzS : (0 : RestartState) ∈ S := by simp [S]
  have H := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => (hreg z hz).differentiableAt (by norm_num))
    (fun z hz => (hbound z hz).1) (convex_closedBall (0 : RestartState) (1 / 16)) hzS hxS
  exact ⟨by simpa only [restartCompactWeakRates_zero, sub_zero] using H, hbound x hxS⟩

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exists_restartMixed_fastLayer_bounds :
    ∃ C ≥ (32 : ℝ), ∀ y : RestartState, ‖restartExpCoordinates y‖ ≤ 1 / 16 →
      ‖fderiv ℝ restartMixedField y‖ ≤ C * ‖restartExpCoordinates y‖ ∧
      ‖fderiv ℝ (fderiv ℝ restartMixedField) y‖ ≤ C ∧
      ‖restartMixedWeakRates y‖ ≤ C * ‖restartExpCoordinates y‖ ∧
      ‖fderiv ℝ restartMixedWeakRates y‖ ≤ C ∧
      ‖fderiv ℝ (fderiv ℝ restartMixedWeakRates) y‖ ≤ C ∧
      -4 < restartMixedField y 0 ∧ restartMixedField y 0 < -2 := by
  obtain ⟨A, _, HA⟩ := exists_restartMixed_derivative_bounds
  obtain ⟨B, hB, HB⟩ := exists_restartCompactWeakRates_bounds
  let C := max 32 (max A (2 * B))
  have hA : A ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have h2B : 2 * B ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hB0 : 0 ≤ B := by linarith only [hB]
  have hBC : B ≤ C := by linarith only [h2B, hB0]
  refine ⟨C, le_max_left _ _, ?_⟩
  intro y hy
  have hn : Real.exp (y 0) ≤ 1 := by
    have H : |Real.exp (y 0)| ≤ 1 / 16 := (norm_le_pi_norm (restartExpCoordinates y) 0).trans hy
    rw [abs_of_pos (Real.exp_pos _)] at H
    linarith only [H]
  have hbox := restartCompact_box_bounds hy
  have hr : 0 < restartRadicand (restartExpCoordinates y) := by linarith only [hbox.2.1]
  have H := composition_second_derivative_bounds (contDiff_restartExpCoordinates 2).contDiffAt
    (contDiffAt_restartCompactWeakRates hr 2) hB0 hB0 (by norm_num : (0 : ℝ) ≤ 1)
    (restartExpCoordinates_derivative_bounds hn).1 (restartExpCoordinates_derivative_bounds hn).2
    (HB _ hy).2.1 (HB _ hy).2.2
  change ‖fderiv ℝ restartMixedWeakRates y‖ ≤ B * 1 ∧
    ‖fderiv ℝ (fderiv ℝ restartMixedWeakRates) y‖ ≤ B * 1 + B * 1 ^ 2 at H
  refine ⟨(HA _ hy).1.trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _)),
    (HA _ hy).2.trans hA,
    (HB _ hy).1.trans (mul_le_mul_of_nonneg_right hBC (norm_nonneg _)),
    by nlinarith only [H.1, hBC], by nlinarith only [H.2, h2B], ?_⟩
  exact hbox.2.2.2.2.2

end
end

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
open Set Filter Metric
open scoped Topology ContDiff

private theorem BianchiIX.contDiffAt_normalizedMaxCurve_smooth {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    ContDiffAt ℝ ∞ (fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 t₀ z.2) (x, t) :=
  contDiffAt_infty.mpr (fun n => contDiffAt_normalizedMaxCurve_nat n ht)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.normalizedMaxCurve_constraint {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    stateConstraint (normalizedMaxCurve x t₀ t) = stateConstraint x := by
  simpa only [normalizedMaxCurve_initial] using
    normalized_constraint_constant (convex_normalizedMaxDomain x t₀)
      (fun _ hu => hasDerivAt_normalizedMaxCurve hu) (initial_mem_normalizedMaxDomain x t₀) ht

end
end

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology

private theorem BianchiIX.contDiffAt_normalizedMaxCurve_two {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    ContDiffAt ℝ 2 (fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 t₀ z.2) (x, t) :=
  (contDiffAt_normalizedMaxCurve_smooth ht).of_le (by decide)

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.le_exp_of_linear_deriv_le {I : Set ℝ} (hI : Convex ℝ I)
    {f f' : ℝ → ℝ} {c s t : ℝ}
    (hf : ∀ u ∈ I, HasDerivAt f (f' u) u) (hbound : ∀ u ∈ I, f' u ≤ c * f u)
    (hs : s ∈ I) (ht : t ∈ I) (hst : s ≤ t) :
    f t ≤ f s * Real.exp (c * (t - s)) := by
  exact le_exp_of_clock_deriv_le hI hf (fun u _ => hasDerivAt_id u)
    (fun u hu => by simpa only [mul_one] using hbound u hu) hs ht hst

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartCompactCenterProjection_norm_le (x : RestartState) :
    ‖restartCompactCenterProjection x‖ ≤ ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro i
  fin_cases i
  · exact norm_le_pi_norm x 1
  · exact norm_le_pi_norm x 2
  · exact norm_le_pi_norm x 3

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartPhysicalCoordinates_norm_le {x : NormalizedState} {R : ℝ} (hR : 0 ≤ R)
    (hn : |x 2| ≤ R) (hZ : ‖restartCenterProjection x‖ ≤ R) :
    ‖restartPhysicalCoordinates x‖ ≤ R := by
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro i
  fin_cases i
  · exact hn
  · exact (norm_le_pi_norm (restartCenterProjection x) 0).trans hZ
  · exact (norm_le_pi_norm (restartCenterProjection x) 1).trans hZ
  · exact (norm_le_pi_norm (restartCenterProjection x) 2).trans hZ

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartCompactField_physical {x : NormalizedState}
    (hc : stateConstraint x = 1) (hp : x 0 < 0) :
    restartCompactField (restartPhysicalCoordinates x) 0 = rateOne (x 0) (x 1) ∧
      restartCompactCenterProjection (restartCompactField (restartPhysicalCoordinates x)) =
        restartCenterProjection (normalizedField x) := by
  have hroot := restart_negative_branch_root hc hp
  have hq : curvature (x 2) (x 3) (x 4) = 1 - shearSq (x 0) (x 1) := by
    dsimp only [stateConstraint, constraint] at hc
    linarith only [hc]
  constructor
  · change curvature (x 2) (x 3) (x 4) - 1 - 2 * Real.sqrt
      (1 - x 1 ^ 2 - curvature (x 2) (x 3) (x 4)) = _
    rw [← hroot, hq]
    dsimp only [rateOne]
    ring
  · ext i
    fin_cases i
    · rfl
    · change x 3 * (curvature (x 2) (x 3) (x 4) - 1 + Real.sqrt
        (1 - x 1 ^ 2 - curvature (x 2) (x 3) (x 4)) + 1 * Real.sqrt 3 * x 1) =
        rateTwo (x 0) (x 1) * x 3
      rw [← hroot, hq]
      dsimp only [rateTwo]
      ring
    · change x 4 * (curvature (x 2) (x 3) (x 4) - 1 + Real.sqrt
        (1 - x 1 ^ 2 - curvature (x 2) (x 3) (x 4)) + (-1) * Real.sqrt 3 * x 1) =
        rateThree (x 0) (x 1) * x 4
      rw [← hroot, hq]
      dsimp only [rateThree]
      ring

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartPhysical_shear_bound {x : NormalizedState}
    (hc : stateConstraint x = 1) (hp : x 0 < 0)
    (hx : ‖restartPhysicalCoordinates x‖ ≤ 1 / 16) : x 0 ≤ -(15 / 16) := by
  have H := (restartCompact_box_bounds hx).2.2.2.1
  have heq : restartCompactRoot (restartPhysicalCoordinates x) = -x 0 :=
    (restart_negative_branch_root hc hp).symm
  rw [heq] at H
  linarith only [H]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartCenterField_bound {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ w : RestartState, ‖w‖ ≤ 1 / 16 → ‖fderiv ℝ restartCompactField w‖ ≤ C * ‖w‖)
    {x : NormalizedState} (hc : stateConstraint x = 1) (hp : x 0 < 0)
    (hn : 0 ≤ x 2 ∧ x 2 ≤ 1 / 16) (hZ : ‖restartCenterProjection x‖ ≤ 1 / 16) :
    ‖restartCenterProjection (normalizedField x)‖ ≤
      C * (x 2 + ‖restartCenterProjection x‖) * ‖restartCenterProjection x‖ := by
  let r := ‖restartCenterProjection x‖
  let R := max (x 2) r
  let w : RestartState := ![x 2, 0, 0, 0]
  let S := Metric.closedBall (0 : RestartState) R
  have hR : 0 ≤ R := hn.1.trans (le_max_left _ _)
  have hRsmall : R ≤ 1 / 16 := max_le hn.2 hZ
  have hRsum : R ≤ x 2 + r := max_le (le_add_of_nonneg_right (norm_nonneg _))
    (le_add_of_nonneg_left hn.1)
  have hxS : restartPhysicalCoordinates x ∈ S := by
    simpa [S] using restartPhysicalCoordinates_norm_le hR
      (by simpa only [abs_of_nonneg hn.1] using le_max_left (x 2) r) (le_max_right (x 2) r)
  have hwS : w ∈ S := by
    change ‖w - 0‖ ≤ R
    rw [sub_zero]
    apply (pi_norm_le_iff_of_nonneg hR).mpr
    intro i
    fin_cases i
    · change |x 2| ≤ R
      rw [abs_of_nonneg hn.1]
      exact le_max_left _ _
    all_goals simpa [w] using hR
  have hdiff (z : RestartState) (hz : z ∈ S) : DifferentiableAt ℝ restartCompactField z := by
    have hzR : ‖z‖ ≤ R := by simpa [S] using hz
    have H := (restartCompact_box_bounds (hzR.trans hRsmall)).2.1
    exact (contDiffAt_restartCompactField (by linarith only [H]) 1).differentiableAt (by norm_num)
  have hbound (z : RestartState) (hz : z ∈ S) : ‖fderiv ℝ restartCompactField z‖ ≤ C * R := by
    have hzR : ‖z‖ ≤ R := by simpa [S] using hz
    exact (hF z (hzR.trans hRsmall)).trans (mul_le_mul_of_nonneg_left hzR hC)
  have H := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hbound (convex_closedBall (0 : RestartState) R) hwS hxS
  have hdist : ‖restartPhysicalCoordinates x - w‖ ≤ r := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg (restartCenterProjection x))).mpr
    intro i
    fin_cases i
    · change |x 2 - x 2| ≤ r
      simpa only [sub_self, abs_zero] using norm_nonneg (restartCenterProjection x)
    · change |x 1 - 0| ≤ r
      rw [sub_zero]
      exact norm_le_pi_norm (restartCenterProjection x) 0
    · change |x 3 - 0| ≤ r
      rw [sub_zero]
      exact norm_le_pi_norm (restartCenterProjection x) 1
    · change |x 4 - 0| ≤ r
      rw [sub_zero]
      exact norm_le_pi_norm (restartCenterProjection x) 2
  have hzero : restartCompactCenterProjection (restartCompactField w) = 0 := by
    ext i
    fin_cases i <;> simp [restartCompactCenterProjection, restartCompactField, w, shearMinus]
  rw [← (restartCompactField_physical hc hp).2]
  have heq : restartCompactCenterProjection (restartCompactField (restartPhysicalCoordinates x)) =
      restartCompactCenterProjection (restartCompactField (restartPhysicalCoordinates x) - restartCompactField w) := by
    rw [map_sub, hzero, sub_zero]
  rw [heq]
  exact (restartCompactCenterProjection_norm_le _).trans
    (H.trans ((mul_le_mul_of_nonneg_left hdist (mul_nonneg hC hR)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRsum hC) (norm_nonneg _))))

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.hasDerivAt_restartFastBudget (C h b t : ℝ) :
    HasDerivAt (restartFastBudget C h b) (C * (h * Real.exp (-2 * t) + b)) t := by
  convert! (((((hasDerivAt_id' t).const_mul (-2)).exp.const_sub 1).const_mul (h / 2)).add
    ((hasDerivAt_id' t).const_mul b)).const_mul C using 1
  ring

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartFastBudget_zero (C h b : ℝ) : restartFastBudget C h b 0 = 0 := by
  simp [restartFastBudget]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartFastBudget_le {C h b T t : ℝ} (hC : 0 ≤ C) (hh : 0 ≤ h) (hb : 0 ≤ b)
    (ht : t ≤ T) : restartFastBudget C h b t ≤ C * h / 2 + C * b * T := by
  have H := mul_nonneg (mul_nonneg hC hh) (Real.exp_pos (-2 * t)).le
  have Ht := mul_le_mul_of_nonneg_left ht (mul_nonneg hC hb)
  dsimp only [restartFastBudget]
  nlinarith only [H, Ht]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exp_one_quarter_lt_two : Real.exp (1 / 4 : ℝ) < 2 := by
  have H := Real.exp_lt_two_add_div_two_sub (x := (1 : ℝ) / 4) (by norm_num) (by norm_num)
  norm_num at H
  linarith only [H]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restart_fastLayer_prefix {C h b T : ℝ} {α : ℝ → NormalizedState}
    (hC : 0 ≤ C)
    (hF : ∀ w : RestartState, ‖w‖ ≤ 1 / 16 → ‖fderiv ℝ restartCompactField w‖ ≤ C * ‖w‖)
    (hh : 2 * h ≤ 1 / 16) (hb : b ≤ 1 / 16)
    (hα : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt α (normalizedField (α t)) t)
    (hc : ∀ t ∈ Icc (0 : ℝ) T, stateConstraint (α t) = 1)
    (hn : ∀ t ∈ Icc (0 : ℝ) T, 0 < α t 2)
    (hregion : ∀ t ∈ Icc (0 : ℝ) T, restartControlRegion h b (α t))
    (hinit : α 0 2 ≤ h) :
    ∀ t ∈ Icc (0 : ℝ) T,
      α t 2 ≤ h * Real.exp (-2 * t) ∧ α t 0 ≤ -(15 / 16) ∧
        ‖restartCenterProjection (α t)‖ ≤
          ‖restartCenterProjection (α 0)‖ * Real.exp (restartFastBudget C h b t) := by
  have hbox (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : ‖restartPhysicalCoordinates (α t)‖ ≤ 1 / 16 :=
    restartPhysicalCoordinates_norm_le (by norm_num)
      (by rw [abs_of_pos (hn t ht)]; exact (hregion t ht).2.1.trans hh) ((hregion t ht).2.2.trans hb)
  have hp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : α t 0 < 0 := by
    have H := (hregion t ht).1
    linarith only [H]
  have hdecay (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : α t 2 ≤ h * Real.exp (-2 * t) := by
    have HD (s : ℝ) (hs : s ∈ Icc (0 : ℝ) t) :=
      (hasDerivAt_normalized_components (hα s ⟨hs.1, hs.2.trans ht.2⟩)).2.2.1
    have HB (s : ℝ) (hs : s ∈ Icc (0 : ℝ) t) :
        rateOne (α s 0) (α s 1) * α s 2 ≤ -2 * α s 2 := by
      have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans ht.2⟩
      have H := (restartCompact_box_bounds (hbox s hsT)).2.2.2.2.2.2
      rw [(restartCompactField_physical (hc s hsT) (hp s hsT)).1] at H
      exact mul_le_mul_of_nonneg_right H.le (hn s hsT).le
    have H := le_exp_of_linear_deriv_le (convex_Icc (0 : ℝ) t) HD HB
      (s := 0) (t := t) ⟨le_rfl, ht.1⟩ ⟨ht.1, le_rfl⟩ ht.1
    have H' : α t 2 ≤ α 0 2 * Real.exp (-2 * t) := by simpa only [sub_zero] using H
    exact H'.trans (mul_le_mul_of_nonneg_right hinit (Real.exp_pos _).le)
  have HD (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      HasDerivAt (fun s => restartCenterProjection (α s))
        (restartCenterProjection (normalizedField (α t))) t := by
    convert! restartCenterProjection.hasFDerivAt.comp_hasDerivAt t (hα t ht) using 1
  have HB (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      ‖restartCenterProjection (normalizedField (α t))‖ ≤
        (C * (h * Real.exp (-2 * t) + b)) * ‖restartCenterProjection (α t)‖ := by
    have H := restartCenterField_bound hC hF (hc t ht) (hp t ht)
      ⟨(hn t ht).le, (hregion t ht).2.1.trans hh⟩ ((hregion t ht).2.2.trans hb)
    exact H.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add (hdecay t ht) (hregion t ht).2.2) hC) (norm_nonneg _))
  have HG := norm_le_exp_of_norm_deriv_clock HD (fun t _ => hasDerivAt_restartFastBudget C h b t) HB
  intro t ht
  refine ⟨hdecay t ht, restartPhysical_shear_bound (hc t ht) (hp t ht) (hbox t ht), ?_⟩
  simpa only [restartFastBudget_zero, sub_zero] using HG t ht

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.isClosed_restartControlRegion (h b : ℝ) : IsClosed {x | restartControlRegion h b x} :=
  (isClosed_le (continuous_apply 0) continuous_const).inter
    ((isClosed_le (continuous_apply 2) continuous_const).inter
      (isClosed_le restartCenterProjection.continuous.norm continuous_const))

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.normalized_restart_fastLayer_control {C h b T : ℝ} {x : NormalizedState}
    (hC : 0 ≤ C)
    (hF : ∀ w : RestartState, ‖w‖ ≤ 1 / 16 → ‖fderiv ℝ restartCompactField w‖ ≤ C * ‖w‖)
    (hh : 0 < h ∧ h ≤ 1 / 128) (hb : 0 < b ∧ b ≤ 1 / 16) (_hT : 0 ≤ T)
    (hbudget : C * h / 2 + C * b * T ≤ 1 / 4)
    (hc : stateConstraint x = 1) (hp : x 0 < 0) (hn : 0 < x 2 ∧ x 2 ≤ h)
    (hZ : ‖restartCenterProjection x‖ ≤ b / 2) :
    ∀ t ∈ Icc (0 : ℝ) T,
      let y := normalizedMaxCurve x 0 t
      0 < y 2 ∧ y 2 ≤ h * Real.exp (-2 * t) ∧ y 0 ≤ -(15 / 16) ∧
        ‖restartCenterProjection y‖ ≤ ‖restartCenterProjection x‖ * Real.exp (restartFastBudget C h b t) ∧
        ‖restartCenterProjection y‖ < b := by
  let α := normalizedMaxCurve x 0
  let S := {t : ℝ | restartControlRegion h b (α t)}
  have hα (t : ℝ) (ht : 0 ≤ t) : HasDerivAt α (normalizedField (α t)) t :=
    (normalizedMaxCurve_forward_of_constraint hc ht).1
  have hcon (t : ℝ) (ht : 0 ≤ t) : stateConstraint (α t) = 1 :=
    (normalizedMaxCurve_forward_of_constraint hc ht).2.1
  have hpos (t : ℝ) (ht : 0 ≤ t) : 0 < α t 2 := by
    have H := normalizedMaxCurve_wall_sign hc ht (0 : Fin 3)
    change (α t 2 = 0 ↔ x 2 = 0) ∧ (0 ≤ α t 2 ↔ 0 ≤ x 2) at H
    have hne : α t 2 ≠ 0 := fun he => hn.1.ne' (H.1.mp he)
    exact lt_of_le_of_ne (H.2.mpr hn.1.le) hne.symm
  have hinit : α 0 = x := normalizedMaxCurve_initial x 0
  have hhsmall : 2 * h ≤ 1 / 16 := by linarith only [hh.2]
  have hZsmall : ‖restartCenterProjection x‖ ≤ 1 / 16 := by linarith only [hZ, hb.2]
  have hpx : x 0 ≤ -(15 / 16) := restartPhysical_shear_bound hc hp
    (restartPhysicalCoordinates_norm_le (by norm_num)
      (by rw [abs_of_pos hn.1]; linarith only [hn.2, hh.2]) hZsmall)
  have hS0 : (0 : ℝ) ∈ S := by
    change restartControlRegion h b (α 0)
    rw [hinit]
    exact ⟨by linarith only [hpx], by linarith only [hn.2, hh.1], by linarith only [hZ, hb.1]⟩
  have hclosed : IsClosed (S ∩ Icc 0 T) := by
    have H := (HasDerivAt.continuousOn (fun t (ht : t ∈ Icc (0 : ℝ) T) => hα t ht.1)).preimage_isClosed_of_isClosed
      isClosed_Icc (isClosed_restartControlRegion h b)
    convert! H using 1
    ext t
    change (restartControlRegion h b (α t) ∧ t ∈ Icc 0 T) ↔
      (t ∈ Icc 0 T ∧ restartControlRegion h b (α t))
    tauto
  have hstrict {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
      (HZ : ‖restartCenterProjection (α t)‖ ≤
        ‖restartCenterProjection (α 0)‖ * Real.exp (restartFastBudget C h b t)) :
      ‖restartCenterProjection (α t)‖ < b := by
    rw [hinit] at HZ
    have HE := (restartFastBudget_le hC hh.1.le hb.1.le ht.2).trans hbudget
    have hbhalf : 0 < b / 2 := div_pos hb.1 (by norm_num)
    have H := HZ.trans (mul_le_mul hZ (Real.exp_le_exp.mpr HE) (Real.exp_pos _).le hbhalf.le)
    have H' := mul_lt_mul_of_pos_left exp_one_quarter_lt_two hbhalf
    nlinarith only [H, H']
  have hwhole : Icc (0 : ℝ) T ⊆ S := by
    apply hclosed.Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset hS0
    intro t ht hbefore
    have H := restart_fastLayer_prefix hC hF hhsmall hb.2
      (fun u hu => hα u hu.1) (fun u hu => hcon u hu.1) (fun u hu => hpos u hu.1)
      (fun u hu => hbefore hu) (by rw [hinit]; exact hn.2) t ⟨ht.1, le_rfl⟩
    have hpstrict : α t 0 < -(1 / 2) := by linarith only [H.2.1]
    have hnstrict : α t 2 < 2 * h := by
      have he := Real.exp_le_one_iff.mpr (by linarith only [ht.1] : -2 * t ≤ 0)
      have Hn := H.1.trans (mul_le_mul_of_nonneg_left he hh.1.le)
      nlinarith only [Hn, hh.1]
    have hZstrict := hstrict ⟨ht.1, ht.2.le⟩ H.2.2
    have hpcont := (continuous_apply (0 : Fin 5)).continuousAt.comp (hα t ht.1).continuousAt
    have hncont := (continuous_apply (2 : Fin 5)).continuousAt.comp (hα t ht.1).continuousAt
    have hZcont := (restartCenterProjection.continuous.continuousAt.comp (hα t ht.1).continuousAt).norm
    have Hev : ∀ᶠ u in 𝓝 t, u ∈ S := by
      filter_upwards [hpcont.eventually (isOpen_Iio.mem_nhds hpstrict),
        hncont.eventually (isOpen_Iio.mem_nhds hnstrict),
        hZcont.eventually (isOpen_Iio.mem_nhds hZstrict)] with u hpu hnu hZu
      exact ⟨hpu.le, hnu.le, hZu.le⟩
    exact Hev.filter_mono nhdsWithin_le_nhds
  have H := restart_fastLayer_prefix hC hF hhsmall hb.2
    (fun u hu => hα u hu.1) (fun u hu => hcon u hu.1) (fun u hu => hpos u hu.1)
    (fun u hu => hwhole hu) (by rw [hinit]; exact hn.2)
  intro t ht
  have Ht := H t ht
  refine ⟨hpos t ht.1, Ht.1, Ht.2.1, ?_, hstrict ht Ht.2.2⟩
  simpa only [hinit] using Ht.2.2

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartMixedChart_constraint {y : RestartState}
    (hy : 0 ≤ restartRadicand (restartExpCoordinates y)) :
    stateConstraint (restartMixedChart y) = 1 := by
  have H := Real.sq_sqrt hy
  dsimp [stateConstraint, constraint, shearSq, restartMixedChart, restartCompactRoot]
  rw [neg_sq, H]
  dsimp [restartRadicand, restartExpCoordinates]
  ring

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartMixedCoordinates_chart (y : RestartState) :
    restartMixedCoordinates (restartMixedChart y) = y := by
  ext i
  fin_cases i <;> simp [restartMixedCoordinates, restartMixedChart, Real.log_exp]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartExpCoordinates_mixed {x : NormalizedState} (hn : 0 < x 2) :
    restartExpCoordinates (restartMixedCoordinates x) = restartPhysicalCoordinates x := by
  ext i
  fin_cases i <;> simp [restartExpCoordinates, restartMixedCoordinates,
    restartPhysicalCoordinates, Real.exp_log hn]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartMixedFlow_initial (y : RestartState) : restartMixedFlow (y, 0) = y := by
  rw [restartMixedFlow, normalizedMaxCurve_initial, restartMixedCoordinates_chart]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_restartMixedChart {y : RestartState}
    (hy : 0 < restartRadicand (restartExpCoordinates y)) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k restartMixedChart y := by
  have hr := (contDiffAt_restartCompactRoot hy k).comp y (contDiff_restartExpCoordinates k).contDiffAt
  rw [contDiffAt_pi]
  intro i
  fin_cases i
  · exact hr.neg
  · exact contDiffAt_apply ℝ ℝ (1 : Fin 4) y
  · exact (contDiffAt_apply ℝ ℝ (0 : Fin 4) y).exp
  · exact contDiffAt_apply ℝ ℝ (2 : Fin 4) y
  · exact contDiffAt_apply ℝ ℝ (3 : Fin 4) y

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_restartMixedCoordinates {x : NormalizedState} (hn : x 2 ≠ 0)
    (k : WithTop ℕ∞) : ContDiffAt ℝ k restartMixedCoordinates x := by
  rw [contDiffAt_pi]
  intro i
  fin_cases i
  · exact (contDiffAt_apply ℝ ℝ (2 : Fin 5) x).log hn
  · exact contDiffAt_apply ℝ ℝ (1 : Fin 5) x
  · exact contDiffAt_apply ℝ ℝ (3 : Fin 5) x
  · exact contDiffAt_apply ℝ ℝ (4 : Fin 5) x

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_restartMixedFlow_two {p : RestartState × ℝ} (hp : restartMixedFlowRegular p) :
    ContDiffAt ℝ 2 restartMixedFlow p := by
  have hc := (contDiffAt_restartMixedChart hp.1 2).comp p contDiffAt_fst
  have hf := (contDiffAt_normalizedMaxCurve_two hp.2.1).comp p (hc.prodMk contDiffAt_snd)
  exact (contDiffAt_restartMixedCoordinates hp.2.2.2.ne' 2).comp p hf

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartMixedFlowRegular_eventually {p : RestartState × ℝ} (hp : restartMixedFlowRegular p) :
    ∀ᶠ q in 𝓝 p, restartMixedFlowRegular q := by
  have hr : ContinuousAt (fun q : RestartState × ℝ => restartRadicand (restartExpCoordinates q.1)) p :=
    ((contDiff_restartRadicand 0).continuous.comp (contDiff_restartExpCoordinates 0).continuous).continuousAt.comp
      continuousAt_fst
  have hc := (contDiffAt_restartMixedChart hp.1 2).comp p contDiffAt_fst
  have he := hc.continuousAt.prodMk continuousAt_snd
  have hf := (contDiffAt_normalizedMaxCurve_two hp.2.1).comp p (hc.prodMk contDiffAt_snd)
  have hpcont := (continuous_apply (0 : Fin 5)).continuousAt.comp hf.continuousAt
  have hncont := (continuous_apply (2 : Fin 5)).continuousAt.comp hf.continuousAt
  filter_upwards [hr.eventually (isOpen_Ioi.mem_nhds hp.1),
    he.eventually ((isOpen_normalizedFlowDomain 0).mem_nhds hp.2.1),
    hpcont.eventually (isOpen_Iio.mem_nhds hp.2.2.1),
    hncont.eventually (isOpen_Ioi.mem_nhds hp.2.2.2)] with q hqr hqd hqp hqn
  exact ⟨hqr, hqd, hqp, hqn⟩

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_restartMixedFlow_time {y : RestartState} {t : ℝ}
    (H : restartMixedFlowRegular (y, t)) :
    HasDerivAt (fun s => restartMixedFlow (y, s)) (restartMixedField (restartMixedFlow (y, t))) t :=
  hasDerivAt_restartMixedCoordinates (hasDerivAt_normalizedMaxCurve H.2.1)
    ((normalizedMaxCurve_constraint H.2.1).trans (restartMixedChart_constraint H.1.le)) H.2.2.1 H.2.2.2

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartMixedFlow_local_partial_time {p : RestartState × ℝ} (hp : restartMixedFlowRegular p) :
    (fun q => fderiv ℝ restartMixedFlow q (0, 1)) =ᶠ[𝓝 p]
      (fun q => restartMixedField (restartMixedFlow q)) := by
  filter_upwards [restartMixedFlowRegular_eventually hp] with q hq
  have hpath : HasDerivAt (fun s : ℝ => (q.1, s)) (0, 1) q.2 :=
    (hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2)
  have HD := ((contDiffAt_restartMixedFlow_two hq).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt
    (f := fun s : ℝ => (q.1, s)) q.2 hpath
  exact HD.unique (hasDerivAt_restartMixedFlow_time hq)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartMixedFlow_radicand_pos {p : RestartState × ℝ} (hp : restartMixedFlowRegular p) :
    0 < restartRadicand (restartExpCoordinates (restartMixedFlow p)) := by
  have hc := (normalizedMaxCurve_constraint hp.2.1).trans (restartMixedChart_constraint hp.1.le)
  have H : restartRadicand (restartPhysicalCoordinates (normalizedMaxCurve (restartMixedChart p.1) 0 p.2)) =
      (normalizedMaxCurve (restartMixedChart p.1) 0 p.2 0) ^ 2 := by
    dsimp [stateConstraint, constraint, shearSq] at hc
    dsimp [restartRadicand, restartPhysicalCoordinates]
    linarith only [hc]
  dsimp only [restartMixedFlow]
  rw [restartExpCoordinates_mixed hp.2.2.2, H]
  exact sq_pos_of_neg hp.2.2.1

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_restartMixedFlow_variation {y : RestartState} {t : ℝ}
    (H : restartMixedFlowRegular (y, t)) (v : RestartState) :
    HasDerivAt (fun s => fderiv ℝ restartMixedFlow (y, s) (v, 0))
      (fderiv ℝ restartMixedField (restartMixedFlow (y, t))
        (fderiv ℝ restartMixedFlow (y, t) (v, 0))) t := by
  have hf : DifferentiableAt ℝ (fun p : ℝ × RestartState => restartMixedField p.2)
      (t, restartMixedFlow (y, t)) :=
    ((contDiffAt_restartMixedField (restartMixedFlow_radicand_pos H) 1).comp
      (t, restartMixedFlow (y, t)) contDiffAt_snd).differentiableAt (by norm_num)
  exact hasDerivAt_parametric_first_variation (contDiffAt_restartMixedFlow_two H) hf
    (restartMixedFlow_local_partial_time H) v

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartMixedFlow_variation_initial {y : RestartState}
    (hy : 0 < restartRadicand (restartExpCoordinates y)) (v : RestartState) :
    fderiv ℝ restartMixedFlow (y, 0) (v, 0) = v := by
  have H : restartMixedFlowRegular (y, 0) := by
    refine ⟨hy, initial_mem_normalizedMaxDomain _ _, ?_, ?_⟩
    · rw [normalizedMaxCurve_initial]
      exact neg_lt_zero.mpr (Real.sqrt_pos.mpr hy)
    · rw [normalizedMaxCurve_initial]
      exact Real.exp_pos _
  rw [← fderiv_parameterSlice_apply ((contDiffAt_restartMixedFlow_two H).differentiableAt (by norm_num)) v]
  simp only [restartMixedFlow_initial, fderiv_fun_id, ContinuousLinearMap.id_apply]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartMixedFlow_fderiv_bound {C h b T : ℝ} {y : RestartState}
    (H : ∀ t ∈ Icc (0 : ℝ) T, restartMixedFlowRegular (y, t))
    (HA : ∀ t ∈ Icc (0 : ℝ) T,
      ‖fderiv ℝ restartMixedField (restartMixedFlow (y, t))‖ ≤ C * (h * Real.exp (-2 * t) + b)) :
    ∀ t ∈ Icc (0 : ℝ) T,
      ‖fderiv ℝ (fun z => restartMixedFlow (z, t)) y‖ ≤ Real.exp (restartFastBudget C h b t) := by
  intro t ht
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le
  intro v
  have HD (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) := hasDerivAt_restartMixedFlow_variation (H s hs) v
  have HB (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
      ‖fderiv ℝ restartMixedField (restartMixedFlow (y, s)) (fderiv ℝ restartMixedFlow (y, s) (v, 0))‖ ≤
        (C * (h * Real.exp (-2 * s) + b)) * ‖fderiv ℝ restartMixedFlow (y, s) (v, 0)‖ :=
    ((fderiv ℝ restartMixedField (restartMixedFlow (y, s))).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (HA s hs) (norm_nonneg _))
  have HG := norm_le_exp_of_norm_deriv_clock HD (fun s _ => hasDerivAt_restartFastBudget C h b s) HB t ht
  rw [restartMixedFlow_variation_initial (H t ht).1, restartFastBudget_zero, sub_zero] at HG
  rw [fderiv_parameterSlice_apply ((contDiffAt_restartMixedFlow_two (H t ht)).differentiableAt (by norm_num)) v]
  simpa only [mul_comm] using HG

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartMixedFlow_fastLayer_regular {C h b T : ℝ} {y : RestartState}
    (hC : 0 ≤ C)
    (hF : ∀ w : RestartState, ‖w‖ ≤ 1 / 16 → ‖fderiv ℝ restartCompactField w‖ ≤ C * ‖w‖)
    (hh : 0 < h ∧ h ≤ 1 / 128) (hb : 0 < b ∧ b ≤ 1 / 16) (hT : 0 ≤ T)
    (hbudget : C * h / 2 + C * b * T ≤ 1 / 4)
    (hn : Real.exp (y 0) ≤ h) (hZ : ‖restartCompactCenterProjection y‖ ≤ b / 2) :
    ∀ t ∈ Icc (0 : ℝ) T, restartMixedFlowRegular (y, t) ∧
      ‖restartExpCoordinates (restartMixedFlow (y, t))‖ ≤ 1 / 16 ∧
      ‖restartExpCoordinates (restartMixedFlow (y, t))‖ ≤ h * Real.exp (-2 * t) + b := by
  have hZsmall : ‖restartCompactCenterProjection y‖ ≤ 1 / 16 := by linarith only [hZ, hb.2]
  have hybox : ‖restartExpCoordinates y‖ ≤ 1 / 16 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 16)).mpr
    intro i
    fin_cases i
    · change |Real.exp (y 0)| ≤ 1 / 16
      rw [abs_of_pos (Real.exp_pos _)]
      linarith only [hn, hh.2]
    · exact (norm_le_pi_norm (restartCompactCenterProjection y) 0).trans hZsmall
    · exact (norm_le_pi_norm (restartCompactCenterProjection y) 1).trans hZsmall
    · exact (norm_le_pi_norm (restartCompactCenterProjection y) 2).trans hZsmall
  have hyrad : 0 < restartRadicand (restartExpCoordinates y) := by
    have H := (restartCompact_box_bounds hybox).2.1
    linarith only [H]
  have hc := restartMixedChart_constraint hyrad.le
  have hp : restartMixedChart y 0 < 0 := neg_lt_zero.mpr (Real.sqrt_pos.mpr hyrad)
  have hcenter : restartCenterProjection (restartMixedChart y) = restartCompactCenterProjection y := by
    ext i
    fin_cases i <;> rfl
  have H := normalized_restart_fastLayer_control hC hF hh hb hT hbudget hc hp
    ⟨Real.exp_pos _, hn⟩ (by rwa [hcenter])
  intro t ht
  have Ht := H t ht
  let x := normalizedMaxCurve (restartMixedChart y) 0 t
  have hpos : 0 < x 2 := Ht.1
  have hreg : restartMixedFlowRegular (y, t) :=
    ⟨hyrad, normalizedMaxDomain_contains_Ici_of_constraint hc 0 ht.1,
      by linarith only [Ht.2.2.1], hpos⟩
  have hnsmall : x 2 ≤ 1 / 16 := by
    have he := Real.exp_le_one_iff.mpr (by linarith only [ht.1] : -2 * t ≤ 0)
    have Hn := Ht.2.1.trans (mul_le_mul_of_nonneg_left he hh.1.le)
    linarith only [Hn, hh.2]
  have hZt : ‖restartCenterProjection x‖ ≤ b := Ht.2.2.2.2.le
  have hexp : restartExpCoordinates (restartMixedFlow (y, t)) = restartPhysicalCoordinates x :=
    restartExpCoordinates_mixed hpos
  refine ⟨hreg, ?_, ?_⟩
  · rw [hexp]
    exact restartPhysicalCoordinates_norm_le (by norm_num)
      (by rwa [abs_of_pos hpos]) (hZt.trans hb.2)
  · rw [hexp]
    have hB : 0 ≤ h * Real.exp (-2 * t) + b :=
      add_nonneg (mul_nonneg hh.1.le (Real.exp_pos _).le) hb.1.le
    apply restartPhysicalCoordinates_norm_le hB
    · rw [abs_of_pos hpos]
      exact Ht.2.1.trans (le_add_of_nonneg_right hb.1.le)
    · exact hZt.trans (le_add_of_nonneg_left (mul_nonneg hh.1.le (Real.exp_pos _).le))

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartMixedFlow_fastLayer_derivative {C h b T : ℝ} {y : RestartState}
    (hC : 0 ≤ C)
    (hF : ∀ w : RestartState, ‖w‖ ≤ 1 / 16 → ‖fderiv ℝ restartCompactField w‖ ≤ C * ‖w‖)
    (hM : ∀ z : RestartState, ‖restartExpCoordinates z‖ ≤ 1 / 16 →
      ‖fderiv ℝ restartMixedField z‖ ≤ C * ‖restartExpCoordinates z‖)
    (hh : 0 < h ∧ h ≤ 1 / 128) (hb : 0 < b ∧ b ≤ 1 / 16) (hT : 0 ≤ T)
    (hbudget : C * h / 2 + C * b * T ≤ 1 / 4)
    (hn : Real.exp (y 0) ≤ h) (hZ : ‖restartCompactCenterProjection y‖ ≤ b / 2) :
    ∀ t ∈ Icc (0 : ℝ) T,
      ContDiffAt ℝ 2 restartMixedFlow (y, t) ∧
      ‖fderiv ℝ (fun z => restartMixedFlow (z, t)) y‖ ≤ Real.exp (1 / 4) ∧
      ‖fderiv ℝ (fun z => restartMixedFlow (z, t)) y‖ < 2 := by
  have H := restartMixedFlow_fastLayer_regular hC hF hh hb hT hbudget hn hZ
  have HA (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      ‖fderiv ℝ restartMixedField (restartMixedFlow (y, t))‖ ≤ C * (h * Real.exp (-2 * t) + b) :=
    (hM _ (H t ht).2.1).trans (mul_le_mul_of_nonneg_left (H t ht).2.2 hC)
  have HD := restartMixedFlow_fderiv_bound (fun t ht => (H t ht).1) HA
  intro t ht
  have HE := (restartFastBudget_le hC hh.1.le hb.1.le ht.2).trans hbudget
  have HB := (HD t ht).trans (Real.exp_le_exp.mpr HE)
  exact ⟨contDiffAt_restartMixedFlow_two (H t ht).1, HB, HB.trans_lt exp_one_quarter_lt_two⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartCenterInclusion_norm (v : RestartCenterState) : ‖restartCenterInclusion v‖ = ‖v‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
    intro i
    fin_cases i
    · change |(0 : ℝ)| ≤ ‖v‖
      simpa only [abs_zero] using norm_nonneg v
    · exact norm_le_pi_norm v 0
    · exact norm_le_pi_norm v 1
    · exact norm_le_pi_norm v 2
  · have heq : restartCompactCenterProjection (restartCenterInclusion v) = v := by
      ext i
      fin_cases i <;> rfl
    simpa only [heq] using restartCompactCenterProjection_norm_le (restartCenterInclusion v)

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.hasFDerivAt_restartMixedSection (h : ℝ) (Z : RestartCenterState) :
    HasFDerivAt (restartMixedSection h) restartCenterInclusion Z := by
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasFDerivAt_const _ _
  · exact hasFDerivAt_apply (𝕜 := ℝ) 0 Z
  · exact hasFDerivAt_apply (𝕜 := ℝ) 1 Z
  · exact hasFDerivAt_apply (𝕜 := ℝ) 2 Z

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartMixedSection_center (h : ℝ) (Z : RestartCenterState) :
    restartCompactCenterProjection (restartMixedSection h Z) = Z := by
  ext i
  fin_cases i <;> rfl

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartMixedChart_section {h : ℝ} (hh : 0 < h) (Z : RestartCenterState) :
    restartMixedChart (restartMixedSection h Z) = restartSectionChart h Z := by
  ext i
  fin_cases i <;> simp [restartMixedChart, restartMixedSection, restartSectionChart,
    restartCompactRoot, restartRadicand, restartExpCoordinates, restartSectionRadicand, Real.exp_log hh]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartSectionMixedFlow_physical {h : ℝ} (hh : 0 < h) (t : ℝ) (Z : RestartCenterState) :
    restartSectionMixedFlow h t Z =
      restartMixedCoordinates (normalizedMaxCurve (restartSectionChart h Z) 0 t) := by
  rw [restartSectionMixedFlow, restartMixedFlow, restartMixedChart_section hh]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.restartWeakMultiplier_pos (T : ℝ) (i : Fin 2) (y : RestartState) :
    0 < restartWeakMultiplier T i y := Real.exp_pos _

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.contDiffAt_restartMixedWeakRates {y : RestartState}
    (hy : 0 < restartRadicand (restartExpCoordinates y)) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k restartMixedWeakRates y :=
  (contDiffAt_restartCompactWeakRates hy k).comp y (contDiff_restartExpCoordinates k).contDiffAt

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.contDiffAt_restartWeakRateIntegrand {p : RestartState × ℝ}
    (H : restartMixedFlowRegular p) (i : Fin 2) :
    ContDiffAt ℝ 2 (restartWeakRateIntegrand i) p :=
  contDiffAt_pi.mp ((contDiffAt_restartMixedWeakRates (restartMixedFlow_radicand_pos H) 2).comp p
    (contDiffAt_restartMixedFlow_two H)) i

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.hasDerivAt_restartMixedFlow_weak {y : RestartState} {t : ℝ}
    (H : restartMixedFlowRegular (y, t)) (i : Fin 2) :
    HasDerivAt (fun s => restartMixedFlow (y, s) (i.addNat 2))
      (restartWeakRateIntegrand i (y, t) * restartMixedFlow (y, t) (i.addNat 2)) t := by
  have HD := (hasDerivAt_pi.mp (hasDerivAt_restartMixedFlow_time H)) (i.addNat 2)
  convert! HD using 1
  fin_cases i <;> simp [restartWeakRateIntegrand, restartMixedWeakRates, restartMixedField,
    Function.comp_apply, restartCompactField, restartCompactWeakRates, restartExpCoordinates,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, mul_comm]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.restartWeakMultiplier_formula {y : RestartState} {T : ℝ} (hT : 0 ≤ T)
    (H : ∀ t ∈ Icc (0 : ℝ) T, restartMixedFlowRegular (y, t)) (i : Fin 2) :
    restartMixedFlow (y, T) (i.addNat 2) = y (i.addNat 2) * restartWeakMultiplier T i y := by
  have hc : ContinuousOn (fun t => restartMixedFlow (y, t) (i.addNat 2)) (Icc (0 : ℝ) T) :=
    HasDerivAt.continuousOn (fun t ht => hasDerivAt_restartMixedFlow_weak (H t ht) i)
  have hr : ContinuousOn (fun t => restartWeakRateIntegrand i (y, t)) (Icc (0 : ℝ) T) :=
    fun t ht => ((contDiffAt_restartWeakRateIntegrand (H t ht) i).continuousAt.comp
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  have HF := homogeneous_solution_eq_exp_integral_Icc hT hr hc
    (fun t ht => hasDerivAt_restartMixedFlow_weak (H t (Ioo_subset_Icc_self ht)) i)
  simpa only [restartMixedFlow_initial, restartWeakMultiplier, restartWeakLogMultiplier] using HF

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.restartWeakRateIntegrand_partial {y : RestartState} {t : ℝ}
    (H : restartMixedFlowRegular (y, t)) (i : Fin 2) (v : RestartState) :
    fderiv ℝ (restartWeakRateIntegrand i) (y, t) (v, 0) =
      fderiv ℝ restartMixedWeakRates (restartMixedFlow (y, t))
        (fderiv ℝ (fun z => restartMixedFlow (z, t)) y v) i := by
  have HF := ((contDiffAt_restartMixedFlow_two H).comp y
    (contDiffAt_id.prodMk (contDiffAt_const (c := t)))).differentiableAt (by norm_num)
  have HG := (contDiffAt_restartMixedWeakRates (restartMixedFlow_radicand_pos H) 2).differentiableAt (by norm_num)
  have HA := (hasFDerivAt_pi'.mp HG.hasFDerivAt i).comp y HF.hasFDerivAt
  have HP := ((contDiffAt_restartWeakRateIntegrand H i).differentiableAt (by norm_num)).hasFDerivAt.comp y
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) y t)
  exact congrArg (fun L : RestartState →L[ℝ] ℝ => L v) (HP.unique HA)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.restartWeakLogMultiplier_regular {y : RestartState} {T : ℝ} (hT : 0 ≤ T)
    (H : ∀ t ∈ Icc (0 : ℝ) T, restartMixedFlowRegular (y, t)) (i : Fin 2) :
    ContDiffAt ℝ 1 (restartWeakLogMultiplier T i) y ∧
      fderiv ℝ (restartWeakLogMultiplier T i) y =
        ∫ t in 0..T, (fderiv ℝ (restartWeakRateIntegrand i) (y, t)).comp
          (ContinuousLinearMap.inl ℝ RestartState ℝ) := by
  have HG (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      ContDiffAt ℝ 1 (restartWeakRateIntegrand i) (y, t) :=
    (contDiffAt_restartWeakRateIntegrand (H t ht) i).of_le (by norm_num)
  exact ⟨contDiffAt_intervalIntegral_of_contDiffAt hT HG,
    (hasFDerivAt_intervalIntegral_of_contDiffAt hT HG).fderiv⟩

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.contDiffAt_restartWeakLogMultiplier_two {y : RestartState} {T : ℝ} (hT : 0 ≤ T)
    (H : ∀ t ∈ Icc (0 : ℝ) T, restartMixedFlowRegular (y, t)) (i : Fin 2) :
    ContDiffAt ℝ 2 (restartWeakLogMultiplier T i) y :=
  contDiffAt_intervalIntegral_two hT (fun t ht => contDiffAt_restartWeakRateIntegrand (H t ht) i)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.restartWeakLogMultiplier_derivative_bound {y : RestartState} {T C : ℝ}
    (hT : 0 ≤ T) (hC : 0 ≤ C)
    (H : ∀ t ∈ Icc (0 : ℝ) T, restartMixedFlowRegular (y, t))
    (HG : ∀ t ∈ Icc (0 : ℝ) T, ‖fderiv ℝ restartMixedWeakRates (restartMixedFlow (y, t))‖ ≤ C)
    (HF : ∀ t ∈ Icc (0 : ℝ) T, ‖fderiv ℝ (fun z => restartMixedFlow (z, t)) y‖ ≤ 2) (i : Fin 2) :
    ‖fderiv ℝ (restartWeakLogMultiplier T i) y‖ ≤ 2 * C * T := by
  rw [(restartWeakLogMultiplier_regular hT H i).2]
  have HI := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := T) (C := 2 * C)
    (f := fun t => (fderiv ℝ (restartWeakRateIntegrand i) (y, t)).comp
      (ContinuousLinearMap.inl ℝ RestartState ℝ)) ?_
  · simpa only [sub_zero, abs_of_nonneg hT] using HI
  · intro t ht
    have ht' : t ∈ Icc (0 : ℝ) T := uIcc_of_le hT ▸ uIoc_subset_uIcc ht
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    change |fderiv ℝ (restartWeakRateIntegrand i) (y, t) (v, 0)| ≤ _
    rw [restartWeakRateIntegrand_partial (H t ht') i v]
    have HV := ((fderiv ℝ (fun z => restartMixedFlow (z, t)) y).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (HF t ht') (norm_nonneg v))
    have HR := (norm_le_pi_norm
      (fderiv ℝ restartMixedWeakRates (restartMixedFlow (y, t))
        (fderiv ℝ (fun z => restartMixedFlow (z, t)) y v)) i).trans
      (((fderiv ℝ restartMixedWeakRates (restartMixedFlow (y, t))).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (HG t ht') (norm_nonneg _)))
    exact HR.trans (by nlinarith only [HV, hC])

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory

private theorem BianchiIX.restartWeakLogMultiplier_budget {y : RestartState} {T C h b : ℝ}
    (hT : 0 ≤ T) (hC : 0 ≤ C) (hh : 0 ≤ h) (hb : 0 ≤ b)
    (HG : ∀ t ∈ Icc (0 : ℝ) T,
      ‖restartMixedWeakRates (restartMixedFlow (y, t))‖ ≤ C * (h * Real.exp (-2 * t) + b)) (i : Fin 2) :
    |restartWeakLogMultiplier T i y| ≤ C * h / 2 + C * b * T := by
  have hc : Continuous (fun t : ℝ => C * (h * Real.exp (-2 * t) + b)) := by fun_prop
  have HI := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
    (f := fun t => restartWeakRateIntegrand i (y, t)) hT
    (Eventually.of_forall fun t (ht : t ∈ Ioc (0 : ℝ) T) =>
      (norm_le_pi_norm (restartMixedWeakRates (restartMixedFlow (y, t))) i).trans (HG t ⟨ht.1.le, ht.2⟩))
    (hc.intervalIntegrable 0 T)
  have HE := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ : t ∈ uIcc (0 : ℝ) T) => hasDerivAt_restartFastBudget C h b t) (hc.intervalIntegrable 0 T)
  rw [HE, restartFastBudget_zero, sub_zero] at HI
  exact HI.trans (restartFastBudget_le hC hh hb le_rfl)

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory

private theorem BianchiIX.restartWeakMultiplier_bounds_of_log {y : RestartState} {T : ℝ} {i : Fin 2}
    (H : |restartWeakLogMultiplier T i y| ≤ 1 / 4) :
    (1 / 2 < restartWeakMultiplier T i y ∧ restartWeakMultiplier T i y < 2) ∧
      (restartWeakMultiplier T i y)⁻¹ < 2 := by
  have hu := (Real.exp_le_exp.mpr (le_abs_self _ |>.trans H)).trans_lt exp_one_quarter_lt_two
  have hl := (Real.exp_le_exp.mpr ((neg_le_abs _).trans H)).trans_lt exp_one_quarter_lt_two
  change restartWeakMultiplier T i y < 2 at hu
  rw [Real.exp_neg] at hl
  change (restartWeakMultiplier T i y)⁻¹ < 2 at hl
  have hp := restartWeakMultiplier_pos T i y
  have Hmul := mul_lt_mul_of_pos_left hl hp
  rw [mul_inv_cancel₀ hp.ne'] at Hmul
  exact ⟨⟨by linarith only [Hmul], hu⟩, hl⟩

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory

private theorem BianchiIX.exists_restartWeakMultiplier_bounds :
    ∃ C ≥ (32 : ℝ), ∀ (h b T : ℝ) (y : RestartState),
      0 < h → C * h ≤ 1 / 4 → (0 < b ∧ b ≤ 1 / 16) → 0 ≤ T → C * b * T ≤ 1 / 8 →
      Real.exp (y 0) ≤ h → ‖restartCompactCenterProjection y‖ ≤ b / 2 →
      ∀ i : Fin 2,
        restartMixedFlow (y, T) (i.addNat 2) = y (i.addNat 2) * restartWeakMultiplier T i y ∧
        |restartWeakLogMultiplier T i y| ≤ 1 / 4 ∧
        (1 / 2 < restartWeakMultiplier T i y ∧ restartWeakMultiplier T i y < 2) ∧
        (restartWeakMultiplier T i y)⁻¹ < 2 ∧
        ContDiffAt ℝ 2 (restartWeakLogMultiplier T i) y ∧
        ContDiffAt ℝ 2 (restartWeakMultiplier T i) y ∧
        ‖fderiv ℝ (restartWeakLogMultiplier T i) y‖ ≤ 2 * C * T ∧
        ‖fderiv ℝ (restartWeakMultiplier T i) y‖ ≤ 4 * C * T := by
  obtain ⟨A, _, HA⟩ := exists_restartCompact_derivative_bounds
  obtain ⟨B, hB, HB⟩ := exists_restartMixed_fastLayer_bounds
  let C := max A B
  have hAC : A ≤ C := le_max_left _ _
  have hBC : B ≤ C := le_max_right _ _
  have hC : 32 ≤ C := hB.trans hBC
  have hC0 : 0 ≤ C := le_trans (by norm_num : (0 : ℝ) ≤ 32) hC
  have hF (w : RestartState) (hw : ‖w‖ ≤ 1 / 16) : ‖fderiv ℝ restartCompactField w‖ ≤ C * ‖w‖ :=
    (HA w hw).1.trans (mul_le_mul_of_nonneg_right hAC (norm_nonneg _))
  have hM (w : RestartState) (hw : ‖restartExpCoordinates w‖ ≤ 1 / 16) :
      ‖fderiv ℝ restartMixedField w‖ ≤ C * ‖restartExpCoordinates w‖ :=
    (HB w hw).1.trans (mul_le_mul_of_nonneg_right hBC (norm_nonneg _))
  refine ⟨C, hC, ?_⟩
  intro h b T y hh hCh hb hT hCb hn hZ i
  have hhsmall : h ≤ 1 / 128 := by
    nlinarith only [hCh, mul_le_mul_of_nonneg_right hC hh.le]
  have hbudget : C * h / 2 + C * b * T ≤ 1 / 4 := by linarith only [hCh, hCb]
  have HR := restartMixedFlow_fastLayer_regular hC0 hF ⟨hh, hhsmall⟩ hb hT hbudget hn hZ
  have HD := restartMixedFlow_fastLayer_derivative hC0 hF hM ⟨hh, hhsmall⟩ hb hT hbudget hn hZ
  have HG (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      ‖restartMixedWeakRates (restartMixedFlow (y, t))‖ ≤ C * (h * Real.exp (-2 * t) + b) :=
    ((HB _ (HR t ht).2.1).2.2.1.trans
      (mul_le_mul_of_nonneg_right hBC (norm_nonneg _))).trans
      (mul_le_mul_of_nonneg_left (HR t ht).2.2 hC0)
  have Hlog := (restartWeakLogMultiplier_budget hT hC0 hh.le hb.1.le HG i).trans hbudget
  have Hbounds := restartWeakMultiplier_bounds_of_log Hlog
  have Hreg := contDiffAt_restartWeakLogMultiplier_two hT (fun t ht => (HR t ht).1) i
  have Hder := restartWeakLogMultiplier_derivative_bound hT hC0 (fun t ht => (HR t ht).1)
    (fun t ht => (HB _ (HR t ht).2.1).2.2.2.1.trans hBC)
    (fun t ht => (HD t ht).2.2.le) i
  refine ⟨restartWeakMultiplier_formula hT (fun t ht => (HR t ht).1) i,
    Hlog, Hbounds.1, Hbounds.2, Hreg, Hreg.exp, Hder, ?_⟩
  have HE := ((Hreg.differentiableAt (by norm_num)).hasFDerivAt.exp).fderiv
  change fderiv ℝ (restartWeakMultiplier T i) y =
    restartWeakMultiplier T i y • fderiv ℝ (restartWeakLogMultiplier T i) y at HE
  rw [HE, norm_smul, Real.norm_eq_abs, abs_of_pos (restartWeakMultiplier_pos T i y)]
  calc
    _ ≤ 2 * ‖fderiv ℝ (restartWeakLogMultiplier T i) y‖ :=
      mul_le_mul_of_nonneg_right Hbounds.1.2.le (norm_nonneg _)
    _ ≤ 4 * C * T := by linarith only [Hder]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiff_restartMixedSection (h : ℝ) (k : WithTop ℕ∞) :
    ContDiff ℝ k (restartMixedSection h) := by
  rw [contDiff_pi]
  intro i
  fin_cases i
  · exact contDiff_const
  · exact contDiff_apply ℝ ℝ (0 : Fin 3)
  · exact contDiff_apply ℝ ℝ (1 : Fin 3)
  · exact contDiff_apply ℝ ℝ (2 : Fin 3)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.fderiv_comp_restartMixedSection_norm_le {f : RestartState → ℝ}
    {h : ℝ} {Z : RestartCenterState} (H : DifferentiableAt ℝ f (restartMixedSection h Z)) :
    ‖fderiv ℝ (fun W => f (restartMixedSection h W)) Z‖ ≤ ‖fderiv ℝ f (restartMixedSection h Z)‖ := by
  have HD := H.hasFDerivAt.comp Z (hasFDerivAt_restartMixedSection h Z)
  change HasFDerivAt (fun W => f (restartMixedSection h W)) _ Z at HD
  rw [HD.fderiv]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  change ‖fderiv ℝ f (restartMixedSection h Z) (restartCenterInclusion v)‖ ≤ _
  simpa only [restartCenterInclusion_norm] using
    (fderiv ℝ f (restartMixedSection h Z)).le_opNorm (restartCenterInclusion v)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exists_restartSectionWeakMultiplier_bounds :
    ∃ C ≥ (32 : ℝ), ∀ (h b T : ℝ),
      0 < h → C * h ≤ 1 / 4 → (0 < b ∧ b ≤ 1 / 16) → 0 ≤ T → C * b * T ≤ 1 / 8 →
      ∀ Z : RestartCenterState, ‖Z‖ ≤ b / 2 → ∀ i : Fin 2,
        normalizedMaxCurve (restartSectionChart h Z) 0 T (i.addNat 3) =
          Z i.succ * restartSectionWeakMultiplier h T i Z ∧
        |restartSectionWeakLogMultiplier h T i Z| ≤ 1 / 4 ∧
        (1 / 2 < restartSectionWeakMultiplier h T i Z ∧ restartSectionWeakMultiplier h T i Z < 2) ∧
        (restartSectionWeakMultiplier h T i Z)⁻¹ < 2 ∧
        ContDiffAt ℝ 2 (restartSectionWeakLogMultiplier h T i) Z ∧
        ContDiffAt ℝ 2 (restartSectionWeakMultiplier h T i) Z ∧
        ‖fderiv ℝ (restartSectionWeakLogMultiplier h T i) Z‖ ≤ 2 * C * T ∧
        ‖fderiv ℝ (restartSectionWeakMultiplier h T i) Z‖ ≤ 4 * C * T := by
  obtain ⟨C, hC, HC⟩ := exists_restartWeakMultiplier_bounds
  refine ⟨C, hC, ?_⟩
  intro h b T hh hCh hb hT hCb Z hZ i
  have H := HC h b T (restartMixedSection h Z) hh hCh hb hT hCb
    (by change Real.exp (Real.log h) ≤ h; rw [Real.exp_log hh])
    (by rwa [restartMixedSection_center]) i
  obtain ⟨Hformula, Hlog, Hbounds, Hinv, Hlogreg, Hreg, HlogD, HD⟩ := H
  have Hsection := (contDiff_restartMixedSection h 2).contDiffAt (x := Z)
  refine ⟨?_, Hlog, Hbounds, Hinv, Hlogreg.comp Z Hsection, Hreg.comp Z Hsection, ?_, ?_⟩
  · change restartSectionMixedFlow h T Z (i.addNat 2) = _ at Hformula
    rw [restartSectionMixedFlow_physical hh] at Hformula
    fin_cases i <;> exact Hformula
  · exact (fderiv_comp_restartMixedSection_norm_le (Hlogreg.differentiableAt (by norm_num))).trans HlogD
  · exact (fderiv_comp_restartMixedSection_norm_le (Hreg.differentiableAt (by norm_num))).trans HD

end
end

private theorem BianchiIX.restartSectionCenterFlow_weak (h T : ℝ) (Z : RestartCenterState) (i : Fin 2) :
    restartSectionCenterFlow h T Z i.succ =
      normalizedMaxCurve (restartSectionChart h Z) 0 T (i.addNat 3) := by
  fin_cases i <;> rfl

/-- Holding an initial weak amplitude fixed preserves that amplitude in the ordinary derivative. -/
theorem solution :
    ∃ C ≥ (32 : ℝ), ∀ h b T : ℝ,
      0 < h → C * h ≤ 1 / 4 → (0 < b ∧ b ≤ 1 / 16) → 0 ≤ T → C * b * T ≤ 1 / 8 →
      ∀ Z : RestartCenterState, ‖Z‖ < b / 2 → ∀ i : Fin 2,
        restartSectionCenterFlow h T Z i.succ = Z i.succ * restartSectionWeakMultiplier h T i Z ∧
        (1 / 2 < restartSectionWeakMultiplier h T i Z ∧ restartSectionWeakMultiplier h T i Z < 2) ∧
        DifferentiableAt ℝ (fun W => restartSectionCenterFlow h T W i.succ) Z ∧
        ∀ v : RestartCenterState, v i.succ = 0 →
          |fderiv ℝ (fun W => restartSectionCenterFlow h T W i.succ) Z v| ≤
            8 * C * T * |restartSectionCenterFlow h T Z i.succ| * ‖v‖ := by
  obtain ⟨C, hC, HC⟩ := exists_restartSectionWeakMultiplier_bounds
  refine ⟨C, hC, ?_⟩
  intro h b T hh hCh hb hT hCb Z hZ i
  obtain ⟨Hformula, _, Hbounds, _, _, Hreg, _, HB⟩ := HC h b T hh hCh hb hT hCb Z hZ.le i
  rw [← restartSectionCenterFlow_weak h T Z i] at Hformula
  have Hnear : ∀ᶠ W : RestartCenterState in 𝓝 Z, ‖W‖ < b / 2 :=
    continuous_norm.continuousAt.eventually (isOpen_Iio.mem_nhds hZ)
  have HE : (fun W => restartSectionCenterFlow h T W i.succ) =ᶠ[𝓝 Z]
      (fun W => W i.succ * restartSectionWeakMultiplier h T i W) := by
    filter_upwards [Hnear] with W hW
    rw [restartSectionCenterFlow_weak]
    exact (HC h b T hh hCh hb hT hCb W hW.le i).1
  have HD := ((hasFDerivAt_apply (𝕜 := ℝ) i.succ Z).mul
    ((Hreg.differentiableAt (by norm_num)).hasFDerivAt)).congr_of_eventuallyEq HE
  have hμ : 0 < restartSectionWeakMultiplier h T i Z := by linarith only [Hbounds.1]
  have Habs : |restartSectionCenterFlow h T Z i.succ| =
      |Z i.succ| * restartSectionWeakMultiplier h T i Z := by
    rw [Hformula, abs_mul, abs_of_pos hμ]
  have HZ : |Z i.succ| ≤ 2 * |restartSectionCenterFlow h T Z i.succ| := by
    nlinarith only [Habs, mul_le_mul_of_nonneg_left Hbounds.1.le (abs_nonneg (Z i.succ))]
  have hC₀ : 0 ≤ C := le_trans (by norm_num : (0 : ℝ) ≤ 32) hC
  refine ⟨Hformula, Hbounds, HD.differentiableAt, ?_⟩
  intro v hv
  rw [HD.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.proj_apply, hv, mul_zero, add_zero]
  have HDμ := ((fderiv ℝ (restartSectionWeakMultiplier h T i) Z).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right HB (norm_nonneg v))
  calc
    _ = |Z i.succ| * |fderiv ℝ (restartSectionWeakMultiplier h T i) Z v| := abs_mul _ _
    _ ≤ (2 * |restartSectionCenterFlow h T Z i.succ|) * ((4 * C * T) * ‖v‖) := by
      exact mul_le_mul HZ HDμ (abs_nonneg _) (by positivity)
    _ = _ := by ring
