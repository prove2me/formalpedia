-- Prove2me | solution 1 for BianchiIX.exists_stableRescaledResidualRate_weighted_decay
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T16:32:06.499521+00:00
-- url     : https://prove2.me/submissions/072d24f4-ae28-4bb1-b67d-fb487cd5304c

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_IntegralClock
import Definitions.Def_BianchiIX_Analysis_SignedRowGrowth
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_StableProjectionRefinementData
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_CompactPhaseExpansionData
import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ProjectiveClock
import Definitions.Def_BianchiIX_Dynamics_Linearization
import Definitions.Def_BianchiIX_Dynamics_ProjectiveOriginalTime
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Theorems.Thm_BianchiIX_abs_le_affine_exp_of_clock_damping
import Theorems.Thm_BianchiIX_contDiffAt_fromProjectiveState
import Theorems.Thm_BianchiIX_contDiffAt_normalizedMaxCurve_nat
import Theorems.Thm_BianchiIX_contDiffAt_projectiveFlowDifferential_one
import Theorems.Thm_BianchiIX_contDiffAt_projectiveOriginalField
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Theorems.Thm_BianchiIX_continuousOn_normalizedProjectiveRate
import Theorems.Thm_BianchiIX_fromProjectiveState_clock_pos
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_hasDerivAt_coordinate_variation
import Theorems.Thm_BianchiIX_hasDerivAt_projectiveFlowDifferential_apply
import Theorems.Thm_BianchiIX_hasDerivAt_projectiveOriginalFlow
import Theorems.Thm_BianchiIX_hasDerivAt_toProjectiveState_normalized
import Theorems.Thm_BianchiIX_integralClock_initial
import Theorems.Thm_BianchiIX_norm_le_exp_of_signedRowSum
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward_of_constraint
import Theorems.Thm_BianchiIX_normalizedMaxCurve_regular
import Theorems.Thm_BianchiIX_normalizedMaxCurve_wall_sign
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_normalized_constraint_constant
import Theorems.Thm_BianchiIX_normalized_stable_global_region
import Theorems.Thm_BianchiIX_projective_chart_differential_inverse
import Theorems.Thm_BianchiIX_reciprocalProfile_derivative_bounds
import Theorems.Thm_BianchiIX_scaled_stable_boundary_drift
import Theorems.Thm_BianchiIX_stableRescaledDifferential_stable_decay
import Theorems.Thm_BianchiIX_stableRescaledDifferential_strong_decay
import Theorems.Thm_BianchiIX_stableRescaledHessian_bound
import Theorems.Thm_BianchiIX_stableRescaledJacobian_center_bounds
import Theorems.Thm_BianchiIX_stableRescaledSecondDifferential_bound
import Theorems.Thm_BianchiIX_stableRescaledSecondDifferential_bound_of_forcing
import Theorems.Thm_BianchiIX_stableRescaledSecondDifferential_strong_decay
import Theorems.Thm_BianchiIX_stableScaledResidualCubic_bounds_of_coefficients
import Theorems.Thm_BianchiIX_toProjectiveState_denom_pos
import Theorems.Thm_BianchiIX_toProjectiveState_fromProjectiveState
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
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.ProjIcc

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

private theorem BianchiIX.fderiv2_mul_apply {f g : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => f y * g y)) x v w =
      f x * fderiv ℝ (fderiv ℝ g) x v w +
        fderiv ℝ f x v * fderiv ℝ g x w +
        fderiv ℝ f x w * fderiv ℝ g x v +
        fderiv ℝ (fderiv ℝ f) x v w * g x := by
  have hf' := (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num)
  have hg' := (hg.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num)
  have hp := ((hf.mul hg).fderiv_right
    (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num)
  have heq : (fun y => fderiv ℝ (fun z => f z * g z) y w) =ᶠ[𝓝 x]
      (fun y => f y * fderiv ℝ g y w + fderiv ℝ f y w * g y) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hfy hgy
    rw [fderiv_fun_mul (hfy.differentiableAt (by norm_num)) (hgy.differentiableAt (by norm_num))]
    simp
    ring
  have Hleft := hp.hasFDerivAt.clm_apply (hasFDerivAt_const w x)
  have Hright := ((hf.differentiableAt (by norm_num)).hasFDerivAt.mul
    (hg'.hasFDerivAt.clm_apply (hasFDerivAt_const w x))).add
    ((hf'.hasFDerivAt.clm_apply (hasFDerivAt_const w x)).mul (hg.differentiableAt (by norm_num)).hasFDerivAt)
  have H := congrArg (fun L : E →L[ℝ] ℝ => L v) (Hleft.unique (Hright.congr_of_eventuallyEq heq))
  simpa [add_assoc, mul_comm, add_comm, add_left_comm] using H

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_reciprocalParameter (n : WithTop ℕ∞) {y : Fin 2 → ℝ} (hy : y 0 + 1 ≠ 0) :
    ContDiffAt ℝ n reciprocalParameter y := by unfold reciprocalParameter; fun_prop

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_reciprocalParameterMap (n : WithTop ℕ∞) {y : Fin 2 → ℝ} (hy : y 0 + 1 ≠ 0) :
    ContDiffAt ℝ n reciprocalParameterMap y := by
  unfold reciprocalParameterMap
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact contDiffAt_reciprocalParameter n hy
  · exact contDiffAt_apply ℝ ℝ 1 y

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.reciprocalParameter_range {y : Fin 2 → ℝ} (hy : 3 / 2 ≤ y 0) :
    0 < reciprocalParameter y ∧ reciprocalParameter y ≤ 2 / 5 := by
  have h : 0 < y 0 + 1 := by linarith
  refine ⟨inv_pos.mpr h, ?_⟩
  dsimp [reciprocalParameter]
  rw [← one_div]
  apply (div_le_iff₀ h).mpr
  linarith

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem BianchiIX.product_second_derivative_bounds {f g : E → ℝ} {x : E} {A B : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf0 : |f x| ≤ A) (hf1 : ‖fderiv ℝ f x‖ ≤ A) (hf2 : ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ A)
    (hg0 : |g x| ≤ B) (hg1 : ‖fderiv ℝ g x‖ ≤ B) (hg2 : ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ B) :
    |f x * g x| ≤ A * B ∧ ‖fderiv ℝ (fun y => f y * g y) x‖ ≤ 2 * A * B ∧
      ‖fderiv ℝ (fderiv ℝ (fun y => f y * g y)) x‖ ≤ 4 * A * B := by
  have hf1' (v : E) : |fderiv ℝ f x v| ≤ A * ‖v‖ :=
    ((fderiv ℝ f x).le_opNorm v).trans (mul_le_mul_of_nonneg_right hf1 (norm_nonneg v))
  have hg1' (v : E) : |fderiv ℝ g x v| ≤ B * ‖v‖ :=
    ((fderiv ℝ g x).le_opNorm v).trans (mul_le_mul_of_nonneg_right hg1 (norm_nonneg v))
  have hf2' (v w : E) : |fderiv ℝ (fderiv ℝ f) x v w| ≤ A * ‖v‖ * ‖w‖ :=
    (((fderiv ℝ (fderiv ℝ f) x) v).le_opNorm w).trans
      (mul_le_mul_of_nonneg_right (((fderiv ℝ (fderiv ℝ f) x).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right hf2 (norm_nonneg v))) (norm_nonneg w))
  have hg2' (v w : E) : |fderiv ℝ (fderiv ℝ g) x v w| ≤ B * ‖v‖ * ‖w‖ :=
    (((fderiv ℝ (fderiv ℝ g) x) v).le_opNorm w).trans
      (mul_le_mul_of_nonneg_right (((fderiv ℝ (fderiv ℝ g) x).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right hg2 (norm_nonneg v))) (norm_nonneg w))
  refine ⟨by rw [abs_mul]; exact mul_le_mul hf0 hg0 (abs_nonneg _) hA, ?_, ?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    rw [fderiv_fun_mul (hf.differentiableAt (by norm_num)) (hg.differentiableAt (by norm_num))]
    change |f x * fderiv ℝ g x v + g x * fderiv ℝ f x v| ≤ _
    have H := abs_add_le (f x * fderiv ℝ g x v) (g x * fderiv ℝ f x v)
    simp only [abs_mul] at H
    nlinarith only [H, mul_le_mul hf0 (hg1' v) (abs_nonneg _) hA,
      mul_le_mul hg0 (hf1' v) (abs_nonneg _) hB]
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro w
    rw [Real.norm_eq_abs, fderiv2_mul_apply hf hg]
    have htri (a b c d : ℝ) : |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
      linarith only [abs_add_le a b, abs_add_le (a + b) c, abs_add_le (a + b + c) d]
    have H := htri (f x * fderiv ℝ (fderiv ℝ g) x v w)
      (fderiv ℝ f x v * fderiv ℝ g x w) (fderiv ℝ f x w * fderiv ℝ g x v)
      (fderiv ℝ (fderiv ℝ f) x v w * g x)
    simp only [abs_mul] at H
    nlinarith only [H, mul_le_mul hf0 (hg2' v w) (abs_nonneg _) hA,
      mul_le_mul (hf1' v) (hg1' w) (abs_nonneg _) (mul_nonneg hA (norm_nonneg v)),
      mul_le_mul (hf1' w) (hg1' v) (abs_nonneg _) (mul_nonneg hA (norm_nonneg w)),
      mul_le_mul (hf2' v w) hg0 (abs_nonneg _) (mul_nonneg (mul_nonneg hA (norm_nonneg v)) (norm_nonneg w))]

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem BianchiIX.clm_precomp_second_derivative_bounds {g : F → ℝ} {x : E} {B : ℝ}
    (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1) (hB : 0 ≤ B) (hg : ContDiffAt ℝ 2 g (L x))
    (hg1 : ‖fderiv ℝ g (L x)‖ ≤ B) (hg2 : ‖fderiv ℝ (fderiv ℝ g) (L x)‖ ≤ B) :
    ‖fderiv ℝ (g ∘ L) x‖ ≤ B ∧ ‖fderiv ℝ (fderiv ℝ (g ∘ L)) x‖ ≤ B := by
  have hLv (v : E) : ‖L v‖ ≤ ‖v‖ :=
    (L.le_opNorm v).trans (mul_le_of_le_one_left (norm_nonneg v) hL)
  have hLd : fderiv ℝ (L : E → F) = fun _ => L := funext (fun _ => L.fderiv)
  constructor
  · rw [fderiv_comp x (hg.differentiableAt (by norm_num)) L.differentiableAt]
    apply ContinuousLinearMap.opNorm_le_bound _ hB
    intro v
    simp only [ContinuousLinearMap.comp_apply, hLd]
    exact ((fderiv ℝ g (L x)).le_opNorm (L v)).trans (mul_le_mul hg1 (hLv v) (norm_nonneg _) hB)
  · apply ContinuousLinearMap.opNorm_le_bound _ hB
    intro v
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hB (norm_nonneg v))
    intro w
    have H := fderiv2_comp_apply L.contDiff.contDiffAt hg v w
    simp only [hLd, fderiv_const_apply, zero_apply, map_zero, zero_add] at H
    rw [H]
    have H0 := (((fderiv ℝ (fderiv ℝ g) (L x)) (L v)).le_opNorm (L w)).trans
      (mul_le_mul_of_nonneg_right ((fderiv ℝ (fderiv ℝ g) (L x)).le_opNorm (L v)) (norm_nonneg (L w)))
    exact H0.trans (mul_le_mul (mul_le_mul hg2 (hLv v) (norm_nonneg _) hB) (hLv w)
      (norm_nonneg _) (mul_nonneg hB (norm_nonneg v)))

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stable_boundary_field (m u w : ℝ) :
    phaseVelocity m u 0 w = m * u ^ 2 - (m + 1) * u * w + w ^ 2 ∧
    strongVelocity m u 0 w = stableStrongRate m u w * u ∧
    activeVelocity m u 0 w = 0 ∧
    weakVelocity m u 0 w = stableWeakRate m u w * w := by
  unfold phaseVelocity strongVelocity activeVelocity weakVelocity coupling
    stableStrongRate stableWeakRate
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  · ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stable_boundary_band {m c : ℝ} (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 10) :
    3 ≤ c + 1 ∧ 5 / 8 * (c + 1) ≤ m ∧ 0 ≤ m ∧ m ≤ c + 1 ∧
      0 ≤ m + 1 ∧ m + 1 ≤ 2 * (c + 1) := by
  obtain ⟨hl, hu⟩ := abs_le.mp hm
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stable_boundary_rates {m c u w : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 10)
    (hu : |u| ≤ 1 / 100) (hw : |w| ≤ 1 / 100) :
    stableStrongRate m u w / (c + 1) ≤ -(c + 1) / 8 ∧
      stableWeakRate m u w / (c + 1) ≤ -(1 / 4) := by
  obtain ⟨hK, hml, hm0, _, _, _⟩ := stable_boundary_band hc hm
  have hK0 : 0 < c + 1 := by linarith
  have hu2 : u ^ 2 ≤ (1 / 100 : ℝ) ^ 2 := sq_le_sq.mpr (by norm_num; exact hu)
  have huw : |u * w| ≤ (1 / 100 : ℝ) ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul hu hw (abs_nonneg _) (by norm_num)
  have hm2 := (sq_le_sq₀ (by positivity : 0 ≤ (5 / 8 : ℝ) * (c + 1)) hm0).mpr hml
  constructor
  · apply (div_le_iff₀ hK0).mpr
    unfold stableStrongRate
    nlinarith [sq_nonneg w, sq_nonneg (c + 1 - 3)]
  · apply (div_le_iff₀ hK0).mpr
    unfold stableWeakRate
    nlinarith [(abs_le.mp huw).1]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stable_boundary_denom {m c u w : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 10)
    (hu : |u| ≤ 1 / 100) (hw : |w| ≤ 1 / 100) :
    0 < projectiveDenom m u 0 w ∧ projectiveDenom m u 0 w ≤ 2 * (c + 1) ^ 2 := by
  obtain ⟨hK, _, hm0, hmK, _, _⟩ := stable_boundary_band hc hm
  have heq : projectiveDenom m u 0 w = 3 + m ^ 2 + (u - w) ^ 2 := by
    unfold projectiveDenom curvature
    ring
  rw [heq]
  have hd : |u - w| ≤ 1 / 50 := (abs_sub _ _).trans (by linarith)
  have hd2 : (u - w) ^ 2 ≤ (1 / 50 : ℝ) ^ 2 := sq_le_sq.mpr (by norm_num; exact hd)
  have hm2 := (sq_le_sq₀ hm0 (by linarith : 0 ≤ c + 1)).mpr hmK
  constructor
  · positivity
  · nlinarith [sq_nonneg (c + 1 - 3)]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_sq (a b : ℝ) : phaseNorm a b ^ 2 = a ^ 2 + b ^ 2 :=
  Real.sq_sqrt (by positivity)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_ge {a b : ℝ} (ha : 0 ≤ a) : a ≤ phaseNorm a b := by
  calc
    a = Real.sqrt (a ^ 2) := (Real.sqrt_sq ha).symm
    _ ≤ phaseNorm a b := Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg b))

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_pos {a b : ℝ} (ha : 0 < a) : 0 < phaseNorm a b :=
  ha.trans_le (phaseNorm_ge ha.le)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableWeakRadius_pos {m w : ℝ} (hm : -1 < m) : 0 < stableWeakRadius m w :=
  phaseNorm_pos (by linarith : 0 < m + 1)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableWeakRadius_sq (m w : ℝ) :
    stableWeakRadius m w ^ 2 = (m + 1) ^ 2 + w ^ 2 := phaseNorm_sq _ _

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableWeakRadius_reciprocal {m w : ℝ} (hm : -1 < m) :
    stableWeakRadius m w = (m + 1) * phaseNorm 1 ((m + 1)⁻¹ * w) := by
  have hL : 0 < m + 1 := by linarith
  have hR : 0 < phaseNorm 1 ((m + 1)⁻¹ * w) := phaseNorm_pos (by norm_num)
  have hsq := phaseNorm_sq 1 ((m + 1)⁻¹ * w)
  have hsq' : ((m + 1) * phaseNorm 1 ((m + 1)⁻¹ * w)) ^ 2 = (m + 1) ^ 2 + w ^ 2 := by
    rw [mul_pow, hsq]
    field_simp
  nlinarith only [hsq', stableWeakRadius_sq m w, stableWeakRadius_pos (w := w) hm,
    mul_pos hL hR]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableResidualCoefficient_compactification (i : Fin 4) {m w : ℝ} (hm : 1 < m) :
    stableResidualCoefficient i ![m, w] =
      (m + 1)⁻¹ * stableResidualProfile i ![(m + 1)⁻¹, w] := by
  have hL : m + 1 ≠ 0 := by linarith
  have hD : m ^ 2 - 1 ≠ 0 := by nlinarith
  have hm1 : m - 1 ≠ 0 := by linarith
  have hden : 1 - 2 * (m + 1)⁻¹ = (m - 1) / (m + 1) := by field_simp; ring
  have hx : 1 - 2 * (m + 1)⁻¹ ≠ 0 := by
    rw [hden]
    exact div_ne_zero (by linarith) hL
  have hR : phaseNorm 1 ((m + 1)⁻¹ * w) ≠ 0 := ne_of_gt (phaseNorm_pos (by norm_num))
  have hR1 : phaseNorm 1 ((m + 1)⁻¹ * w) + 1 ≠ 0 := by
    have H := phaseNorm_pos (a := (1 : ℝ)) (b := (m + 1)⁻¹ * w) (by norm_num)
    linarith
  fin_cases i <;>
    dsimp [stableResidualCoefficient, stableResidualProfile, stableResidual4,
      stableResidual3, stableResidual2, stableResidual1] <;>
    (try rw [stableWeakRadius_reciprocal (by linarith : -1 < m)]) <;>
    (try rw [hden]) <;>
    field_simp <;> ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_stableResidualProfile (n : WithTop ℕ∞) (i : Fin 4) {p : Fin 2 → ℝ}
    (hp : p 0 < 1 / 2) : ContDiffAt ℝ n (stableResidualProfile i) p := by
  have hd : 1 - 2 * p 0 ≠ 0 := by linarith
  have hd2 := pow_ne_zero 2 hd
  have hs : (1 : ℝ) ^ 2 + (p 0 * p 1) ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hR : phaseNorm 1 (p 0 * p 1) ≠ 0 := ne_of_gt (phaseNorm_pos (by norm_num))
  have hR1 : phaseNorm 1 (p 0 * p 1) + 1 ≠ 0 := by
    have H := phaseNorm_pos (a := (1 : ℝ)) (b := p 0 * p 1) (by norm_num)
    linarith
  dsimp [phaseNorm] at hR hR1
  have hRR := mul_ne_zero hR hR1
  fin_cases i <;> unfold stableResidualProfile <;> dsimp [phaseNorm] <;> fun_prop

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_stableResidualProfile_bounds :
    ∃ B > (0 : ℝ), ∀ p : Fin 2 → ℝ, (0 ≤ p 0 ∧ p 0 ≤ 2 / 5) → |p 1| ≤ 1 →
      ∀ i : Fin 4, |stableResidualProfile i p| ≤ B ∧
        ‖fderiv ℝ (stableResidualProfile i) p‖ ≤ B ∧
        ‖fderiv ℝ (fderiv ℝ (stableResidualProfile i)) p‖ ≤ B := by
  let S : Set (Fin 2 → ℝ) := Icc ![0, -1] ![2 / 5, 1]
  have hS : IsCompact S := isCompact_Icc
  let q := fun (p : Fin 2 → ℝ) (i : Fin 4) => |stableResidualProfile i p| +
    ‖fderiv ℝ (stableResidualProfile i) p‖ + ‖fderiv ℝ (fderiv ℝ (stableResidualProfile i)) p‖
  have hq (p : Fin 2 → ℝ) (i : Fin 4) : 0 ≤ q p i := by dsimp [q]; positivity
  have hcont (i : Fin 4) : ContinuousOn (fun p => q p i) S := by
    intro p hp
    have hreg := contDiffAt_stableResidualProfile 2 i (p := p) (by have H := hp.2 0; dsimp at H; linarith)
    have hreg' := hreg.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    exact ((hreg.continuousAt.abs.add (hreg.continuousAt_fderiv (by norm_num)).norm).add
      (hreg'.continuousAt_fderiv (by norm_num)).norm).continuousWithinAt
  have hsum : ContinuousOn (fun p => ∑ i : Fin 4, q p i) S :=
    continuousOn_finsetSum _ (fun i _ => hcont i)
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hsum
  refine ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro p hp hw i
  have hpS : p ∈ S := by
    constructor
    · intro j; fin_cases j
      · exact hp.1
      · exact (abs_le.mp hw).1
    · intro j; fin_cases j
      · exact hp.2
      · exact (abs_le.mp hw).2
  have H : q p i ≤ max B 1 :=
    (Finset.single_le_sum (fun j _ => hq p j) (Finset.mem_univ i)).trans
      ((le_abs_self _).trans ((hB p hpS).trans (le_max_left _ _)))
  dsimp [q] at H
  exact ⟨by linarith [norm_nonneg (fderiv ℝ (stableResidualProfile i) p),
      norm_nonneg (fderiv ℝ (fderiv ℝ (stableResidualProfile i)) p)],
    by linarith [abs_nonneg (stableResidualProfile i p),
      norm_nonneg (fderiv ℝ (fderiv ℝ (stableResidualProfile i)) p)],
    by linarith [abs_nonneg (stableResidualProfile i p), norm_nonneg (fderiv ℝ (stableResidualProfile i) p)]⟩

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.stableResidualCoefficient_reciprocal (i : Fin 4) {y : Fin 2 → ℝ} (hy : 1 < y 0) :
    stableResidualCoefficient i y = reciprocalParameter y * stableResidualProfile i (reciprocalParameterMap y) := by
  change _ = (y 0 + 1)⁻¹ * stableResidualProfile i ![(y 0 + 1)⁻¹, y 1]
  rw [← stableResidualCoefficient_compactification i hy]
  congr 1
  ext j
  fin_cases j <;> rfl

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.stableResidualCoefficient_eventually_reciprocal (i : Fin 4) {y : Fin 2 → ℝ} (hy : 1 < y 0) :
    stableResidualCoefficient i =ᶠ[𝓝 y]
      (fun z => reciprocalParameter z * stableResidualProfile i (reciprocalParameterMap z)) := by
  filter_upwards [(continuous_apply 0).continuousAt.eventually (isOpen_Ioi.mem_nhds hy)] with z hz
  exact stableResidualCoefficient_reciprocal i hz

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.exists_stableResidualCoefficient_derivative_bounds :
    ∃ C > (0 : ℝ), ∀ y : Fin 2 → ℝ, 3 / 2 ≤ y 0 → |y 1| ≤ 1 → ∀ i : Fin 4,
      ContDiffAt ℝ 2 (stableResidualCoefficient i) y ∧
        |stableResidualCoefficient i y| ≤ C / (y 0 + 1) ∧
        ‖fderiv ℝ (stableResidualCoefficient i) y‖ ≤ C / (y 0 + 1) ∧
        ‖fderiv ℝ (fderiv ℝ (stableResidualCoefficient i)) y‖ ≤ C / (y 0 + 1) := by
  obtain ⟨B, hB, HB⟩ := exists_stableResidualProfile_bounds
  refine ⟨7 * B, by positivity, ?_⟩
  intro y hy hw i
  have ha := reciprocalParameter_range hy
  have hcoords : 0 ≤ reciprocalParameterMap y 0 ∧ reciprocalParameterMap y 0 ≤ 2 / 5 := ⟨ha.1.le, ha.2⟩
  obtain ⟨h0, h1, h2⟩ := HB (reciprocalParameterMap y) hcoords hw i
  have hn : y 0 + 1 ≠ 0 := by linarith
  have hp := contDiffAt_stableResidualProfile 2 i (p := reciprocalParameterMap y) (by dsimp [reciprocalParameterMap]; linarith [ha.2])
  have heq := stableResidualCoefficient_eventually_reciprocal i (by linarith : 1 < y 0)
  have hreg := (contDiffAt_reciprocalParameter 2 hn).mul
    (hp.comp y (contDiffAt_reciprocalParameterMap 2 hn))
  refine ⟨hreg.congr_of_eventuallyEq heq, ?_⟩
  obtain ⟨H0, H1, H2⟩ := reciprocalProfile_derivative_bounds hy hB.le hp h0 h1 h2
  rw [heq.eq_of_nhds, heq.fderiv_eq, heq.fderiv.fderiv_eq]
  have hnonneg : 0 ≤ B * reciprocalParameter y := mul_nonneg hB.le ha.1.le
  simp only [reciprocalParameter, div_eq_mul_inv] at H0 H1 H2 hnonneg ⊢
  exact ⟨by nlinarith only [H0, hnonneg], by nlinarith only [H1, hnonneg], H2⟩

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.exists_stableResidualCoefficient_band_derivative_bounds :
    ∃ C > (0 : ℝ), ∀ (c : ℝ) (y : Fin 2 → ℝ), 2 ≤ c → |y 0 - c| ≤ 1 / 10 → |y 1| ≤ 1 →
      ∀ i : Fin 4, ContDiffAt ℝ 2 (stableResidualCoefficient i) y ∧
        |stableResidualCoefficient i y| ≤ C / (c + 1) ∧
        ‖fderiv ℝ (stableResidualCoefficient i) y‖ ≤ C / (c + 1) ∧
        ‖fderiv ℝ (fderiv ℝ (stableResidualCoefficient i)) y‖ ≤ C / (c + 1) := by
  obtain ⟨C, hC, HC⟩ := exists_stableResidualCoefficient_derivative_bounds
  refine ⟨2 * C, by positivity, ?_⟩
  intro c y hc hm hw i
  have hml := (abs_le.mp hm).1
  have hy : 3 / 2 ≤ y 0 := by linarith
  obtain ⟨hreg, h0, h1, h2⟩ := HC y hy hw i
  have H : C / (y 0 + 1) ≤ (2 * C) / (c + 1) := by
    apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
    nlinarith [hC]
  exact ⟨hreg, h0.trans H, h1.trans H, h2.trans H⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.hasFDerivAt_normalizedMaxCurve_initial {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    HasFDerivAt (fun y => normalizedMaxCurve y t₀ t) (normalizedFlowDifferential x t₀ t) x := by
  have H := (normalizedMaxCurve_regular ht).2.comp x (contDiffAt_id.prodMk contDiffAt_const)
  exact (H.differentiableAt (by norm_num)).hasFDerivAt

end
end

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology

private theorem BianchiIX.normalizedFlowDifferential_initial (x : NormalizedState) (t₀ : ℝ) :
    normalizedFlowDifferential x t₀ t₀ = ContinuousLinearMap.id ℝ NormalizedState := by
  simp [normalizedFlowDifferential, normalizedMaxCurve_initial]

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
open Set Filter
open scoped Topology

private theorem BianchiIX.projectiveFlowDifferential_initial {y : ProjectiveState} (hD : 0 < projectiveStateDenom y) (t₀ : ℝ) :
    projectiveFlowDifferential y t₀ t₀ = ContinuousLinearMap.id ℝ ProjectiveState := by
  rw [projectiveFlowDifferential, normalizedMaxCurve_initial, normalizedFlowDifferential_initial,
    ContinuousLinearMap.id_comp, projective_chart_differential_inverse hD]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasFDerivAt_projectiveOriginalFlow_initial {y : ProjectiveState} {t₀ t : ℝ}
    (hD : 0 < projectiveStateDenom y) (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0) :
    HasFDerivAt (fun z => projectiveOriginalFlow z t₀ t) (projectiveFlowDifferential y t₀ t) y := by
  have hfrom := ((contDiffAt_fromProjectiveState 1 (ne_of_gt hD)).differentiableAt (by norm_num)).hasFDerivAt
  have hto := ((contDiffAt_toProjectiveState 1 (ne_of_gt hA)).differentiableAt (by norm_num)).hasFDerivAt
  exact hto.comp y ((hasFDerivAt_normalizedMaxCurve_initial ht).comp y hfrom)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_projectiveOriginalFlow_time {y : ProjectiveState} {t₀ t : ℝ}
    (hD : 0 < projectiveStateDenom y) (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0) :
    HasDerivAt (projectiveOriginalFlow y t₀)
      (projectiveOriginalField (projectiveOriginalFlow y t₀ t)) t := by
  have hc : stateConstraint (normalizedMaxCurve (fromProjectiveState y) t₀ t) = 1 :=
    (normalizedMaxCurve_constraint ht).trans (fromProjectiveState_constraint (ne_of_gt hD))
  exact hasDerivAt_projectiveOriginalFlow (hasDerivAt_normalizedMaxCurve ht) (ne_of_gt hA) hc

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.contDiffAt_projectiveOriginalFlow_two {y : ProjectiveState} {t₀ t : ℝ}
    (hD : 0 < projectiveStateDenom y) (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0) :
    ContDiffAt ℝ 2 (fun z : ProjectiveState × ℝ => projectiveOriginalFlow z.1 t₀ z.2) (y, t) := by
  have hparam : ContDiffAt ℝ 2 (fun z : ProjectiveState × ℝ => (fromProjectiveState z.1, z.2)) (y, t) :=
    ((contDiffAt_fromProjectiveState 2 (ne_of_gt hD)).comp (y, t) contDiffAt_fst).prodMk contDiffAt_snd
  have hN : ContDiffAt ℝ 2 (fun z : ProjectiveState × ℝ => normalizedMaxCurve (fromProjectiveState z.1) t₀ z.2) (y, t) := by
    simpa only [Function.comp_def] using (contDiffAt_normalizedMaxCurve_two ht).comp (y, t) hparam
  simpa only [Function.comp_def, projectiveOriginalFlow] using
    (contDiffAt_toProjectiveState 2 (ne_of_gt hA)).comp (y, t) hN

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.abs_le_exp_of_clock_damping {f d z z' : ℝ → ℝ} {a b c : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (z' t * (d t * f t)) t)
    (hz : ∀ t ∈ Icc a b, HasDerivAt z (z' t) t)
    (hzpos : ∀ t ∈ Icc a b, 0 ≤ z' t)
    (hd : ∀ t ∈ Icc a b, d t ≤ -c) :
    ∀ t ∈ Icc a b, |f t| ≤ |f a| * Real.exp (-c * (z t - z a)) := by
  have H := abs_le_affine_exp_of_clock_damping (g := fun _ => 0) (B := 0)
    (by simpa only [add_zero] using hf) hz hzpos hd (by simp)
  simpa only [zero_mul, mul_zero, add_zero, mul_comm] using H

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.scaled_stable_boundary_decay {Y : ℝ → ProjectiveState} {a z : ℝ → ℝ}
    {s t c : ℝ} (hc : 2 ≤ c)
    (hY : ∀ r ∈ Icc s t, HasDerivAt Y (a r • projectiveField (Y r)) r)
    (hz : ∀ r ∈ Icc s t, HasDerivAt z ((c + 1) * a r) r)
    (ha : ∀ r ∈ Icc s t, 0 ≤ a r)
    (hv : ∀ r ∈ Icc s t, Y r 2 = 0)
    (hm : ∀ r ∈ Icc s t, |Y r 0 - c| ≤ 1 / 10)
    (hu : ∀ r ∈ Icc s t, |Y r 1| ≤ 1 / 100)
    (hw : ∀ r ∈ Icc s t, |Y r 3| ≤ 1 / 100) :
    ∀ r ∈ Icc s t,
      |Y r 1| ≤ |Y s 1| * Real.exp (-(c + 1) / 8 * (z r - z s)) ∧
      |Y r 3| ≤ |Y s 3| * Real.exp (-(1 / 4) * (z r - z s)) := by
  have hK : 0 < c + 1 := by linarith
  have hcoord (i : Fin 4) (r : ℝ) (hr : r ∈ Icc s t) := hasDerivAt_pi.mp (hY r hr) i
  have hU (r : ℝ) (hr : r ∈ Icc s t) :
      HasDerivAt (fun q => Y q 1)
        (((c + 1) * a r) * (stableStrongRate (Y r 0) (Y r 1) (Y r 3) / (c + 1) * Y r 1)) r := by
    convert! hcoord 1 r hr using 1
    change _ = a r * strongVelocity (Y r 0) (Y r 1) (Y r 2) (Y r 3)
    rw [hv r hr, (stable_boundary_field (Y r 0) (Y r 1) (Y r 3)).2.1]
    field_simp
  have hW (r : ℝ) (hr : r ∈ Icc s t) :
      HasDerivAt (fun q => Y q 3)
        (((c + 1) * a r) * (stableWeakRate (Y r 0) (Y r 1) (Y r 3) / (c + 1) * Y r 3)) r := by
    convert! hcoord 3 r hr using 1
    change _ = a r * weakVelocity (Y r 0) (Y r 1) (Y r 2) (Y r 3)
    rw [hv r hr, (stable_boundary_field (Y r 0) (Y r 1) (Y r 3)).2.2.2]
    field_simp
  have H := abs_le_exp_of_clock_damping hU hz (fun r hr => mul_nonneg hK.le (ha r hr))
    (fun r hr => by simpa only [neg_div] using (stable_boundary_rates hc (hm r hr) (hu r hr) (hw r hr)).1)
  have J := abs_le_exp_of_clock_damping hW hz (fun r hr => mul_nonneg hK.le (ha r hr))
    (fun r hr => (stable_boundary_rates hc (hm r hr) (hu r hr) (hw r hr)).2)
  intro r hr
  exact ⟨by simpa only [neg_div] using H r hr, J r hr⟩

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.hasDerivAt_normalizedStableClock {x : NormalizedState} {t₀ s c t : ℝ}
    (hs : s ∈ normalizedMaxDomain x t₀) (ht : t ∈ normalizedMaxDomain x t₀) :
    HasDerivAt (normalizedStableClock x t₀ s c)
      ((c + 1) * normalizedProjectiveRate x t₀ t) t :=
  ((hasStrictDerivAt_integralClock (convex_normalizedMaxDomain x t₀)
    (isOpen_normalizedMaxDomain x t₀) (continuousOn_normalizedProjectiveRate x t₀) hs ht).hasDerivAt).const_mul _

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.normalized_stable_prefix_estimates {x : NormalizedState} {t₀ s t c : ℝ}
    (hx : stateConstraint x = 1) (hc : 2 ≤ c) (hs : t₀ ≤ s) (hst : s ≤ t)
    (hA : ∀ r ∈ Icc s t, 0 < normalizedProjectiveRate x t₀ r)
    (hy : ∀ r ∈ Icc s t, stableBoundaryRegion c (toProjectiveState (normalizedMaxCurve x t₀ r))) :
    let Y := fun r => toProjectiveState (normalizedMaxCurve x t₀ r)
    |Y t 0 - Y s 0| ≤ 8 * (|Y s 1| + |Y s 3|) ^ 2 / (c + 1) ∧
    (∀ r ∈ Icc s t,
      |Y r 1| ≤ |Y s 1| * Real.exp (-(c + 1) / 8 * normalizedStableClock x t₀ s c r) ∧
      |Y r 3| ≤ |Y s 3| * Real.exp (-(1 / 4) * normalizedStableClock x t₀ s c r)) ∧
    (∀ r ∈ Icc s t, |Y r 1| ≤ |Y s 1| ∧ |Y r 3| ≤ |Y s 3|) := by
  intro Y
  have hdom (r : ℝ) (hr : s ≤ r) : r ∈ normalizedMaxDomain x t₀ :=
    normalizedMaxDomain_contains_Ici_of_constraint hx t₀ (hs.trans hr)
  have hY (r : ℝ) (hr : r ∈ Icc s t) :
      HasDerivAt Y (normalizedProjectiveRate x t₀ r • projectiveField (Y r)) r := by
    have H := normalizedMaxCurve_forward_of_constraint hx (hs.trans hr.1)
    exact hasDerivAt_toProjectiveState_normalized H.1 (ne_of_gt (hA r hr)) H.2.1
  have hz (r : ℝ) (hr : r ∈ Icc s t) :=
    hasDerivAt_normalizedStableClock (c := c) (hdom s le_rfl) (hdom r hr.1)
  have hac : ContinuousOn (normalizedProjectiveRate x t₀) (Icc s t) :=
    (continuousOn_normalizedProjectiveRate x t₀).mono (fun r hr => hdom r hr.1)
  have H := scaled_stable_boundary_decay hc hY hz (fun r hr => (hA r hr).le)
    (fun r hr => (hy r hr).2.2.1) (fun r hr => (hy r hr).1)
    (fun r hr => (hy r hr).2.1) (fun r hr => (hy r hr).2.2.2)
  have hzero : normalizedStableClock x t₀ s c s = 0 := by
    simp [normalizedStableClock, integralClock_initial]
  simp only [hzero, sub_zero] at H
  refine ⟨scaled_stable_boundary_drift hst hc hY hz hac (fun r hr => (hA r hr).le)
    (fun r hr => (hy r hr).2.2.1) (fun r hr => (hy r hr).1)
    (fun r hr => (hy r hr).2.1) (fun r hr => (hy r hr).2.2.2), H, ?_⟩
  intro r hr
  have hz0 : 0 ≤ normalizedStableClock x t₀ s c r := by
    apply mul_nonneg (by linarith : 0 ≤ c + 1)
    apply intervalIntegral.integral_nonneg hr.1
    intro q hq
    exact (hA q ⟨hq.1, hq.2.trans hr.2⟩).le
  constructor
  · exact (H r hr).1.trans (mul_le_of_le_one_right (abs_nonneg _)
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) hz0)))
  · exact (H r hr).2.trans (mul_le_of_le_one_right (abs_nonneg _)
      (Real.exp_le_one_iff.mpr (by linarith)))

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.normalizedStableClock_lower {x : NormalizedState} {t₀ s t c : ℝ}
    (hx : stateConstraint x = 1) (hc : 2 ≤ c) (hs : t₀ ≤ s) (hst : s ≤ t)
    (hA : ∀ r ∈ Icc s t, 3 / (c + 1) ^ 2 ≤ normalizedProjectiveRate x t₀ r) :
    3 / (c + 1) * (t - s) ≤ normalizedStableClock x t₀ s c t := by
  have hK : 0 < c + 1 := by linarith
  have hcA : ContinuousOn (normalizedProjectiveRate x t₀) (Icc s t) :=
    (continuousOn_normalizedProjectiveRate x t₀).mono
      (fun r hr => normalizedMaxDomain_contains_Ici_of_constraint hx t₀ (hs.trans hr.1))
  have H := intervalIntegral.integral_mono_on (μ := volume) hst (intervalIntegrable_const (c := 3 / (c + 1) ^ 2))
    (hcA.intervalIntegrable_of_Icc hst) hA
  rw [intervalIntegral.integral_const] at H
  have H' := mul_le_mul_of_nonneg_left H hK.le
  convert! H' using 1
  simp only [smul_eq_mul]
  field_simp

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.stableBoundaryEntry_denom_pos (m u w : ℝ) :
    0 < projectiveStateDenom (stableBoundaryEntry m u w) := by
  change 0 < projectiveDenom m u 0 w
  have H : projectiveDenom m u 0 w = 3 + m ^ 2 + (u - w) ^ 2 := by
    unfold projectiveDenom curvature
    ring
  rw [H]
  positivity

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.stableBoundaryOrbit_initial (m u w : ℝ) :
    stableBoundaryOrbit m u w 0 = stableBoundaryEntry m u w := by
  unfold stableBoundaryOrbit
  rw [normalizedMaxCurve_initial]
  exact toProjectiveState_fromProjectiveState (ne_of_gt (stableBoundaryEntry_denom_pos m u w))

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.stableBoundaryOrbit_global {m c u w : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 40)
    (hu : |u| ≤ 1 / 200) (hw : |w| ≤ 1 / 200) :
    ∀ t ≥ 0,
      3 / (c + 1) ^ 2 ≤ normalizedProjectiveRate (fromProjectiveState (stableBoundaryEntry m u w)) 0 t ∧
      stableBoundaryRegion c (stableBoundaryOrbit m u w t) ∧
      |stableBoundaryOrbit m u w t 0 - m| ≤ 8 * (|u| + |w|) ^ 2 / (c + 1) ∧
      |stableBoundaryOrbit m u w t 1| ≤ |u| ∧ |stableBoundaryOrbit m u w t 3| ≤ |w| := by
  have hD := stableBoundaryEntry_denom_pos m u w
  have hx := fromProjectiveState_constraint (ne_of_gt hD)
  have hA : 0 < normalizedProjectiveRate (fromProjectiveState (stableBoundaryEntry m u w)) 0 0 := by
    unfold normalizedProjectiveRate
    rw [normalizedMaxCurve_initial]
    exact fromProjectiveState_clock_pos hD
  have hi := stableBoundaryOrbit_initial m u w
  have H := normalized_stable_global_region hx hc (le_refl 0) hA
  change |stableBoundaryOrbit m u w 0 0 - c| ≤ 1 / 40 →
    |stableBoundaryOrbit m u w 0 1| ≤ 1 / 200 → stableBoundaryOrbit m u w 0 2 = 0 →
    |stableBoundaryOrbit m u w 0 3| ≤ 1 / 200 → _ at H
  have H' := H (by simpa [hi, stableBoundaryEntry] using hm)
    (by simpa [hi, stableBoundaryEntry] using hu) (by simp [hi, stableBoundaryEntry])
    (by simpa [hi, stableBoundaryEntry] using hw)
  change ∀ t ≥ 0, _ ∧ stableBoundaryRegion c (stableBoundaryOrbit m u w t) ∧
    |stableBoundaryOrbit m u w t 0 - stableBoundaryOrbit m u w 0 0| ≤
      8 * (|stableBoundaryOrbit m u w 0 1| + |stableBoundaryOrbit m u w 0 3|) ^ 2 / (c + 1) ∧
    |stableBoundaryOrbit m u w t 1| ≤ |stableBoundaryOrbit m u w 0 1| ∧
    |stableBoundaryOrbit m u w t 3| ≤ |stableBoundaryOrbit m u w 0 3| at H'
  simpa [hi, stableBoundaryEntry] using H'

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_stableBoundaryOrbit_two {y : Fin 3 → ℝ} {c t : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (ht : 0 ≤ t) :
    ContDiffAt ℝ 2 (fun z : (Fin 3 → ℝ) × ℝ => stableBoundaryOrbit (z.1 0) (z.1 1) (z.1 2) z.2) (y, t) := by
  have hD := stableBoundaryEntry_denom_pos (y 0) (y 1) (y 2)
  have hx := fromProjectiveState_constraint (ne_of_gt hD)
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint hx 0 ht
  have hK : 0 < c + 1 := by linarith
  have hA := lt_of_lt_of_le (by positivity : 0 < 3 / (c + 1) ^ 2)
    (stableBoundaryOrbit_global hc hm hu hw t ht).1
  have hentry : ContDiffAt ℝ 2
      (fun z : (Fin 3 → ℝ) × ℝ => (stableBoundaryEntry (z.1 0) (z.1 1) (z.1 2), z.2)) (y, t) := by
    apply ContDiffAt.prodMk _ contDiffAt_snd
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i <;> dsimp [stableBoundaryEntry] <;> fun_prop
  have H := (contDiffAt_projectiveOriginalFlow_two hD hdom hA).comp (y, t) hentry
  exact H

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableInclusion_apply (y : StableState) : stableInclusion y = ![y 0, y 1, 0, y 2] := by
  ext i
  fin_cases i <;> rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableRestriction_apply (y : ProjectiveState) : stableRestriction y = ![y 0, y 1, y 3] := by
  ext i
  fin_cases i <;> rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableInclusion_entry (y : StableState) :
    stableInclusion y = stableBoundaryEntry (y 0) (y 1) (y 2) := stableInclusion_apply y

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableRestriction_inclusion (y : StableState) : stableRestriction (stableInclusion y) = y := by
  ext i
  fin_cases i <;> rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableInclusion_restriction {y : ProjectiveState} (hy : y 2 = 0) :
    stableInclusion (stableRestriction y) = y := by
  ext i
  fin_cases i
  · rfl
  · rfl
  · exact hy.symm
  · rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableBoundaryDenom_pos (y : StableState) : 0 < stableBoundaryDenom y := by
  unfold stableBoundaryDenom
  positivity

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableBoundaryDenom_eq (y : StableState) :
    projectiveStateDenom (stableInclusion y) = stableBoundaryDenom y := by
  change projectiveDenom (y 0) (y 1) 0 (y 2) = _
  unfold projectiveDenom curvature stableBoundaryDenom
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableBoundaryField_inclusion (y : StableState) :
    projectiveField (stableInclusion y) = stableInclusion (stableBoundaryField y) := by
  obtain ⟨hM, hU, hV, hW⟩ := stable_boundary_field (y 0) (y 1) (y 2)
  ext i
  fin_cases i
  · exact hM
  · exact hU
  · exact hV
  · exact hW

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableOriginalField_inclusion (y : StableState) :
    projectiveOriginalField (stableInclusion y) = stableInclusion (stableOriginalField y) := by
  rw [projectiveOriginalField, stableBoundaryDenom_eq, stableBoundaryField_inclusion,
    stableOriginalField, map_smul]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableOriginalField_restriction {y : ProjectiveState} (hy : y 2 = 0) :
    stableRestriction (projectiveOriginalField y) = stableOriginalField (stableRestriction y) := by
  rw [← stableInclusion_restriction hy, stableOriginalField_inclusion, stableRestriction_inclusion,
    stableRestriction_inclusion]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiff_stableBoundaryField (n : WithTop ℕ∞) : ContDiff ℝ n stableBoundaryField := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [stableBoundaryField, stableStrongRate, stableWeakRate] <;> fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiff_stableBoundaryDenom (n : WithTop ℕ∞) : ContDiff ℝ n stableBoundaryDenom := by
  unfold stableBoundaryDenom
  fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiff_stableOriginalField (n : WithTop ℕ∞) : ContDiff ℝ n stableOriginalField := by
  apply (contDiff_const.div (contDiff_stableBoundaryDenom n)
    (fun y => ne_of_gt (stableBoundaryDenom_pos y))).smul (contDiff_stableBoundaryField n)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.stableBoundaryOrbit_active_zero (m u w : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    stableBoundaryOrbit m u w t 2 = 0 := by
  let x := fromProjectiveState (stableBoundaryEntry m u w)
  have hx : stateConstraint x = 1 := fromProjectiveState_constraint (ne_of_gt (stableBoundaryEntry_denom_pos m u w))
  have hzero : wallValue 1 x = 0 := by
    simp [x, wallValue, fromProjectiveState, stableBoundaryEntry]
  have H := (normalizedMaxCurve_wall_sign hx ht 1).1.mpr hzero
  change normalizedMaxCurve x 0 t 3 = 0 at H
  change Real.sqrt 3 * normalizedMaxCurve x 0 t 3 / (1 + normalizedMaxCurve x 0 t 0) = 0
  rw [H, mul_zero, zero_div]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.stableOriginalFlow_eq (y : StableState) (t : ℝ) :
    stableOriginalFlow y t = stableRestriction (stableBoundaryOrbit (y 0) (y 1) (y 2) t) := by
  simp only [stableOriginalFlow, stableInclusion_entry, projectiveOriginalFlow, stableBoundaryOrbit]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.stableProjectiveFlow_active_zero (y : StableState) {t : ℝ} (ht : 0 ≤ t) :
    projectiveOriginalFlow (stableInclusion y) 0 t 2 = 0 := by
  simpa only [stableInclusion_entry, projectiveOriginalFlow, stableBoundaryOrbit] using
    stableBoundaryOrbit_active_zero (y 0) (y 1) (y 2) ht

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.stableProjectiveFlow_rate_pos {y : StableState} {c t : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (ht : 0 ≤ t) :
    0 < normalizedProjectiveRate (fromProjectiveState (stableInclusion y)) 0 t := by
  have hK : 0 < c + 1 := by linarith
  rw [stableInclusion_entry]
  exact lt_of_lt_of_le (by positivity : 0 < 3 / (c + 1) ^ 2)
    (stableBoundaryOrbit_global hc hm hu hw t ht).1

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.stableFlowDifferential_initial (y : StableState) :
    stableFlowDifferential y 0 = ContinuousLinearMap.id ℝ StableState := by
  rw [stableFlowDifferential, projectiveFlowDifferential_initial
    (by rw [stableBoundaryDenom_eq]; exact stableBoundaryDenom_pos y), ContinuousLinearMap.id_comp]
  ext v i
  exact congrFun (stableRestriction_inclusion v) i

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasFDerivAt_stableOriginalFlow {y : StableState} {c t : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (ht : 0 ≤ t) :
    HasFDerivAt (fun z => stableOriginalFlow z t) (stableFlowDifferential y t) y := by
  have hD : 0 < projectiveStateDenom (stableInclusion y) := by
    rw [stableBoundaryDenom_eq]
    exact stableBoundaryDenom_pos y
  have hx := fromProjectiveState_constraint (ne_of_gt hD)
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint hx 0 ht
  have hA := stableProjectiveFlow_rate_pos hc hm hu hw ht
  have H := stableRestriction.hasFDerivAt.comp y
    ((hasFDerivAt_projectiveOriginalFlow_initial hD hdom hA).comp y stableInclusion.hasFDerivAt)
  exact H

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_stableFlowDifferential_apply {y : StableState} {c t : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (ht : 0 ≤ t) (v : StableState) :
    HasDerivAt (fun s => stableFlowDifferential y s v)
      (fderiv ℝ stableOriginalField (stableOriginalFlow y t) (stableFlowDifferential y t v)) t := by
  let alpha := projectiveOriginalFlow (stableInclusion y) 0
  let V := fun s => projectiveFlowDifferential (stableInclusion y) 0 s (stableInclusion v)
  let b := fun z : StableState => projectiveOriginalFlow (stableInclusion z) 0 t
  have hD : 0 < projectiveStateDenom (stableInclusion y) := by
    rw [stableBoundaryDenom_eq]
    exact stableBoundaryDenom_pos y
  have hx := fromProjectiveState_constraint (ne_of_gt hD)
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint hx 0 ht
  have hA := stableProjectiveFlow_rate_pos hc hm hu hw ht
  have hb := (hasFDerivAt_projectiveOriginalFlow_initial hD hdom hA).comp y stableInclusion.hasFDerivAt
  have halpha := hasDerivAt_projectiveOriginalFlow_time hD hdom hA
  have hV := hasDerivAt_projectiveFlowDifferential_apply hD hdom hA (stableInclusion v)
  have hDout : 0 < projectiveStateDenom (alpha t) := by
    have hcon := (normalizedMaxCurve_constraint hdom).trans (fromProjectiveState_constraint (ne_of_gt hD))
    exact toProjectiveState_denom_pos hA hcon
  have heq : (fun z => fderiv ℝ stableRestriction (b z) (projectiveOriginalField (b z))) =ᶠ[𝓝 y]
      (fun z => stableOriginalField (stableRestriction (b z))) := by
    apply Eventually.of_forall
    intro z
    simp only [stableRestriction.fderiv]
    exact stableOriginalField_restriction (stableProjectiveFlow_active_zero z ht)
  have H := hasDerivAt_coordinate_variation stableRestriction.contDiff.contDiffAt
    ((contDiffAt_projectiveOriginalField 1 hDout.ne').differentiableAt (by norm_num))
    ((contDiff_stableOriginalField 1).differentiable (by norm_num) (stableRestriction (alpha t)))
    halpha hV hb rfl rfl heq
  simpa only [stableRestriction.fderiv, stableFlowDifferential, stableOriginalFlow, alpha,
    ContinuousLinearMap.comp_apply] using H

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_stableBoundaryField {gamma : ℝ → StableState} {v : StableState} {t : ℝ}
    (h : HasDerivAt gamma v t) :
    HasDerivAt (fun s => stableBoundaryField (gamma s))
      ((stableBoundaryJacobian (gamma t)).mulVec v) t := by
  have hm := hasDerivAt_pi.mp h 0
  have hu := hasDerivAt_pi.mp h 1
  have hw := hasDerivAt_pi.mp h 2
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · apply (((hm.mul (hu.pow 2)).sub (((hm.add_const 1).mul hu).mul hw)).add
      (hw.pow 2)).congr_deriv
    simp [stableBoundaryJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  · apply ((((((hasDerivAt_const t (1 : ℝ)).sub (hm.pow 2)).sub
      (hw.pow 2)).add (hu.pow 2)).div_const 2).mul hu).congr_deriv
    simp [stableBoundaryJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  · apply ((((hm.add_const 1).add (hu.mul hw)).sub (hu.pow 2)).neg.mul hw).congr_deriv
    simp [stableBoundaryJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_stableBoundaryDenom {gamma : ℝ → StableState} {v : StableState} {t : ℝ}
    (h : HasDerivAt gamma v t) :
    HasDerivAt (fun s => stableBoundaryDenom (gamma s))
      (dotProduct (stableDenomGradient (gamma t)) v) t := by
  have hm := hasDerivAt_pi.mp h 0
  have hu := hasDerivAt_pi.mp h 1
  have hw := hasDerivAt_pi.mp h 2
  apply (((hm.pow 2).const_add 3).add ((hu.sub hw).pow 2)).congr_deriv
  simp [stableDenomGradient, dotProduct, Fin.sum_univ_succ]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_stableOriginalField {gamma : ℝ → StableState} {v : StableState} {t : ℝ}
    (h : HasDerivAt gamma v t) :
    HasDerivAt (fun s => stableOriginalField (gamma s))
      ((stableOriginalJacobian (gamma t)).mulVec v) t := by
  have hd := hasDerivAt_stableBoundaryDenom h
  have hf := hasDerivAt_stableBoundaryField h
  apply (((hasDerivAt_const t (6 : ℝ)).div hd
    (stableBoundaryDenom_pos (gamma t)).ne').smul hf).congr_deriv
  ext i
  simp [stableOriginalJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableOriginalField_fderiv (y v : StableState) :
    fderiv ℝ stableOriginalField y v = (stableOriginalJacobian y).mulVec v := by
  have hl : HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1
    simp
  have hf := ((contDiff_stableOriginalField 1).differentiable (by norm_num) y).hasFDerivAt
  have hzero : y + (0 : ℝ) • v = y := by simp
  have H := (hzero.symm ▸ hf).comp_hasDerivAt 0 hl
  simpa only [hzero] using H.unique (hasDerivAt_stableOriginalField hl)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableFlow_variational_equation {y : StableState} {c t : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (ht : 0 ≤ t) (v : StableState) :
    HasDerivAt (fun s => stableFlowDifferential y s v)
      ((stableOriginalJacobian (stableOriginalFlow y t)).mulVec (stableFlowDifferential y t v)) t := by
  simpa only [stableOriginalField_fderiv] using
    hasDerivAt_stableFlowDifferential_apply hc hm hu hw ht v

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableDenomGradient_dotProduct (y v : StableState) :
    dotProduct (stableDenomGradient y) v =
      2 * y 0 * v 0 + 2 * (y 1 - y 2) * (v 1 - v 2) := by
  simp [stableDenomGradient, dotProduct, Fin.sum_univ_succ]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_stableDenomGradient_dotProduct
    {gamma : ℝ → StableState} {v : StableState} {t : ℝ}
    (h : HasDerivAt gamma v t) (w : StableState) :
    HasDerivAt (fun s => dotProduct (stableDenomGradient (gamma s)) w)
      (stableDenomHessian v w) t := by
  simp only [stableDenomGradient_dotProduct]
  have hm := hasDerivAt_pi.mp h 0
  have hu := hasDerivAt_pi.mp h 1
  have hw := hasDerivAt_pi.mp h 2
  exact ((hm.const_mul 2).mul_const (w 0)).add
    (((hu.sub hw).const_mul 2).mul_const (w 1 - w 2))

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.stableRescaledDifferential_initial (K : ℝ) (y : StableState) :
    stableRescaledDifferential K y 0 = ContinuousLinearMap.id ℝ StableState := by
  simp only [stableRescaledDifferential, mul_zero, stableFlowDifferential_initial]

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.hasFDerivAt_stableRescaledFlow {K : ℝ} {y : StableState} {c s : ℝ}
    (hK : 0 < K) (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) :
    HasFDerivAt (fun z => stableRescaledFlow K z s) (stableRescaledDifferential K y s) y :=
  hasFDerivAt_stableOriginalFlow hc hm hu hw (mul_nonneg hK.le hs)

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.stableRescaledFlow_variational_equation {K : ℝ} {y : StableState} {c s : ℝ}
    (hK : 0 < K) (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) (v : StableState) :
    HasDerivAt (fun r => stableRescaledDifferential K y r v)
      (K • (stableOriginalJacobian (stableRescaledFlow K y s)).mulVec
        (stableRescaledDifferential K y s v)) s := by
  exact (stableFlow_variational_equation hc hm hu hw (mul_nonneg hK.le hs) v).scomp s
    (by simpa using (hasDerivAt_id s).const_mul K)

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_stableOriginalFlow_two {y : StableState} {c t : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (ht : 0 ≤ t) :
    ContDiffAt ℝ 2 (fun z : StableState × ℝ => stableOriginalFlow z.1 z.2) (y, t) := by
  simp_rw [stableOriginalFlow_eq]
  exact stableRestriction.contDiff.contDiffAt.comp (y, t)
    (contDiffAt_stableBoundaryOrbit_two hc hm hu hw ht)

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_stableRescaledFlow_two {K : ℝ} {y : StableState} {c s : ℝ}
    (hK : 0 < K) (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) :
    ContDiffAt ℝ 2 (fun z : StableState × ℝ => stableRescaledFlow K z.1 z.2) (y, s) := by
  have H := contDiffAt_stableOriginalFlow_two hc hm hu hw (mul_nonneg hK.le hs)
  have hmap : ContDiffAt ℝ 2 (fun z : StableState × ℝ => (z.1, K * z.2)) (y, s) :=
    contDiffAt_fst.prodMk (contDiffAt_const.mul contDiffAt_snd)
  have H' := H.comp (y, s) hmap
  exact H'

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableBoundary_rate_denom_bounds {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) :
    |stableStrongRate (y 0) (y 1) (y 2)| ≤ stableBoundaryDenom y ∧
      |stableWeakRate (y 0) (y 1) (y 2)| ≤ stableBoundaryDenom y := by
  have hK : 0 < c + 1 := by linarith
  have hr := stable_boundary_rates hc hm hu hw
  have hs := (div_le_iff₀ hK).mp hr.1
  have hw' := (div_le_iff₀ hK).mp hr.2
  have hs0 : stableStrongRate (y 0) (y 1) (y 2) ≤ 0 := by nlinarith
  have hw0 : stableWeakRate (y 0) (y 1) (y 2) ≤ 0 := by nlinarith
  rw [abs_of_nonpos hs0, abs_of_nonpos hw0]
  have huw : |y 1 * y 2| ≤ (1 / 100 : ℝ) ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul hu hw (abs_nonneg _) (by norm_num)
  obtain ⟨huwl, huwu⟩ := abs_le.mp huw
  unfold stableStrongRate stableWeakRate stableBoundaryDenom
  constructor
  · nlinarith [sq_nonneg (y 0), sq_nonneg (y 1), sq_nonneg (y 2)]
  · nlinarith [sq_nonneg (y 0 - 1 / 2), sq_nonneg (y 1), sq_nonneg (y 2)]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableBoundary_field_div_bounds {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) :
    |stableBoundaryField y 1 / stableBoundaryDenom y| ≤ |y 1| ∧
      |stableBoundaryField y 2 / stableBoundaryDenom y| ≤ |y 2| := by
  have H := stableBoundary_rate_denom_bounds hc hm hu hw
  have hD := stableBoundaryDenom_pos y
  constructor
  · rw [abs_div, abs_of_pos hD]
    apply (div_le_iff₀ hD).mpr
    change |stableStrongRate (y 0) (y 1) (y 2) * y 1| ≤ _
    rw [abs_mul, mul_comm _ (stableBoundaryDenom y)]
    exact mul_le_mul_of_nonneg_right H.1 (abs_nonneg _)
  · rw [abs_div, abs_of_pos hD]
    apply (div_le_iff₀ hD).mpr
    change |stableWeakRate (y 0) (y 1) (y 2) * y 2| ≤ _
    rw [abs_mul, mul_comm _ (stableBoundaryDenom y)]
    exact mul_le_mul_of_nonneg_right H.2 (abs_nonneg _)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableBoundary_polynomial_rows {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) :
    stableBoundaryJacobian y 1 1 + |stableBoundaryJacobian y 1 2| +
        4 * (|y 1| + |y 2|) ^ 2 ≤ -(c + 1) ^ 2 / 16 ∧
    stableBoundaryJacobian y 2 2 + |stableBoundaryJacobian y 2 1| +
        4 * (|y 1| + |y 2|) ^ 2 ≤ -(c + 1) / 8 := by
  have hK : 0 < c + 1 := by linarith
  have hr := stable_boundary_rates hc hm hu hw
  have hs := (div_le_iff₀ hK).mp hr.1
  have hw' := (div_le_iff₀ hK).mp hr.2
  have hb : (|y 1| + |y 2|) ^ 2 ≤ (1 / 50 : ℝ) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by norm_num)).mpr (by linarith)
  have hu2 : y 1 ^ 2 ≤ (1 / 100 : ℝ) ^ 2 :=
    sq_le_sq.mpr (by norm_num; exact hu)
  have huw : |y 1 * y 2| ≤ (1 / 100 : ℝ) ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul hu hw (abs_nonneg _) (by norm_num)
  have hcross : |(2 * y 1 - y 2) * y 2| ≤ 3 / 10000 := by
    rw [abs_mul]
    have H : |2 * y 1 - y 2| ≤ 3 / 100 := by
      have H' := abs_sub (2 * y 1) (y 2)
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at H'
      linarith
    nlinarith [mul_le_mul H hw (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 3 / 100)]
  constructor
  · change (1 - y 0 ^ 2 - y 2 ^ 2 + 3 * y 1 ^ 2) / 2 + |-y 1 * y 2| + _ ≤ _
    rw [neg_mul, abs_neg]
    unfold stableStrongRate at hs
    nlinarith [sq_nonneg (c + 1 - 3)]
  · change -(y 0 + 1 + 2 * y 1 * y 2 - y 1 ^ 2) + |(2 * y 1 - y 2) * y 2| + _ ≤ _
    unfold stableWeakRate at hw'
    nlinarith [(abs_le.mp huw).1]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableOriginalJacobian_factor (y : StableState) (i j : Fin 3) :
    stableOriginalJacobian y i j = 6 / stableBoundaryDenom y *
      (stableBoundaryJacobian y i j - stableBoundaryField y i / stableBoundaryDenom y *
        stableDenomGradient y j) := by
  unfold stableOriginalJacobian
  field_simp [(stableBoundaryDenom_pos y).ne']

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stable_rational_row {a d f g h D b : ℝ}
    (hD : 0 < D) (hb : 0 ≤ b) (hf : |f / D| ≤ b) (hg : |g| ≤ 2 * b) (hh : |h| ≤ 2 * b) :
    6 / D * (a - f / D * g) + |6 / D * (d - f / D * h)| ≤
      6 / D * (a + |d| + 4 * b ^ 2) := by
  have h1 : |f / D * g| ≤ 2 * b ^ 2 := by
    rw [abs_mul]
    nlinarith [mul_le_mul hf hg (abs_nonneg _) hb]
  have h2 : |f / D * h| ≤ 2 * b ^ 2 := by
    rw [abs_mul]
    nlinarith [mul_le_mul hf hh (abs_nonneg _) hb]
  rw [abs_mul, abs_of_pos (by positivity : 0 < 6 / D)]
  have H : a - f / D * g + |d - f / D * h| ≤ a + |d| + 4 * b ^ 2 := by
    have H' := abs_sub d (f / D * h)
    nlinarith [(abs_le.mp h1).1]
  have H' := mul_le_mul_of_nonneg_left H (by positivity : 0 ≤ 6 / D)
  nlinarith only [H']

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableOriginalJacobian_stable_rows {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) :
    stableOriginalJacobian y 1 1 + |stableOriginalJacobian y 1 2| ≤
        6 / stableBoundaryDenom y * (-(c + 1) ^ 2 / 16) ∧
    stableOriginalJacobian y 2 2 + |stableOriginalJacobian y 2 1| ≤
        6 / stableBoundaryDenom y * (-(c + 1) / 8) := by
  have hD := stableBoundaryDenom_pos y
  have hf := stableBoundary_field_div_bounds hc hm hu hw
  have hr := stableBoundary_polynomial_rows hc hm hu hw
  have hb : 0 ≤ |y 1| + |y 2| := by positivity
  have hg1 : |stableDenomGradient y 1| ≤ 2 * (|y 1| + |y 2|) := by
    change |2 * (y 1 - y 2)| ≤ _
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left (abs_sub _ _) (by norm_num)
  have hg2 : |stableDenomGradient y 2| ≤ 2 * (|y 1| + |y 2|) := by
    change |2 * (y 2 - y 1)| ≤ _
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have H := abs_sub (y 2) (y 1)
    linarith
  simp_rw [stableOriginalJacobian_factor]
  constructor
  · exact (stable_rational_row hD hb (hf.1.trans (by linarith [abs_nonneg (y 2)])) hg1 hg2).trans
      (mul_le_mul_of_nonneg_left hr.1 (by positivity))
  · exact (stable_rational_row hD hb (hf.2.trans (by linarith [abs_nonneg (y 1)])) hg2 hg1).trans
      (mul_le_mul_of_nonneg_left hr.2 (by positivity))

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableRescaledJacobian_stable_rows {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) :
    (c + 1) * (stableOriginalJacobian y 1 1 + |stableOriginalJacobian y 1 2|) ≤
        -3 * (c + 1) / 16 ∧
    (c + 1) * (stableOriginalJacobian y 2 2 + |stableOriginalJacobian y 2 1|) ≤
        -(3 / 8) := by
  have hK : 0 < c + 1 := by linarith
  have hD := stableBoundaryDenom_pos y
  have hDup : stableBoundaryDenom y ≤ 2 * (c + 1) ^ 2 := by
    have H := (stable_boundary_denom hc hm hu hw).2
    change projectiveStateDenom (stableBoundaryEntry (y 0) (y 1) (y 2)) ≤ _ at H
    rwa [← stableInclusion_entry, stableBoundaryDenom_eq] at H
  have H := stableOriginalJacobian_stable_rows hc hm hu hw
  constructor
  · apply (mul_le_mul_of_nonneg_left H.1 hK.le).trans
    have heq : (c + 1) * (6 / stableBoundaryDenom y * (-(c + 1) ^ 2 / 16)) =
        (-3 * (c + 1) ^ 3 / 8) / stableBoundaryDenom y := by ring
    rw [heq]
    apply (div_le_iff₀ hD).mpr
    nlinarith [mul_le_mul_of_nonneg_left hDup hK.le]
  · apply (mul_le_mul_of_nonneg_left H.2 hK.le).trans
    have heq : (c + 1) * (6 / stableBoundaryDenom y * (-(c + 1) / 8)) =
        (-3 * (c + 1) ^ 2 / 4) / stableBoundaryDenom y := by ring
    rw [heq]
    apply (div_le_iff₀ hD).mpr
    linarith

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_stableRescaledDifferential_one {K : ℝ} {y : StableState} {c s : ℝ}
    (hK : 0 < K) (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) :
    ContDiffAt ℝ 1 (fun z : StableState × ℝ => stableRescaledDifferential K z.1 z.2) (y, s) := by
  have hD : 0 < projectiveStateDenom (stableInclusion y) := by
    rw [stableBoundaryDenom_eq]
    exact stableBoundaryDenom_pos y
  have ht := mul_nonneg hK.le hs
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint
    (fromProjectiveState_constraint hD.ne') 0 ht
  have hA := stableProjectiveFlow_rate_pos hc hm hu hw ht
  have hp : ContDiffAt ℝ 1
      (fun z : StableState × ℝ => (stableInclusion z.1, K * z.2)) (y, s) :=
    (stableInclusion.contDiff.contDiffAt.comp (y, s) contDiffAt_fst).prodMk
      (contDiffAt_const.mul contDiffAt_snd)
  have H := (contDiffAt_projectiveFlowDifferential_one hD hdom hA).comp (y, s) hp
  exact contDiffAt_const.clm_comp (H.clm_comp contDiffAt_const)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasFDerivAt_stableRescaledDifferential {K : ℝ} {y : StableState} {c s : ℝ}
    (hK : 0 < K) (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) :
    HasFDerivAt (fun z => stableRescaledDifferential K z s)
      (stableRescaledSecondDifferential K y s) y := by
  have H := ((contDiffAt_stableRescaledDifferential_one hK hc hm hu hw hs).differentiableAt
    (by norm_num)).hasFDerivAt
  exact H.comp y (hasFDerivAt_prodMk_left (𝕜 := ℝ) y s)

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.stableRescaledFlow_band {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) :
    |stableRescaledFlow (c + 1) y s 0 - c| ≤ 1 / 10 ∧
    |stableRescaledFlow (c + 1) y s 1| ≤ 1 / 100 ∧
    |stableRescaledFlow (c + 1) y s 2| ≤ 1 / 100 := by
  have ht : 0 ≤ (c + 1) * s := mul_nonneg (by linarith) hs
  have H := (stableBoundaryOrbit_global hc hm hu hw ((c + 1) * s) ht).2.1
  simp only [stableRescaledFlow, stableOriginalFlow_eq, stableRestriction_apply]
  exact ⟨H.1, H.2.1, H.2.2.2⟩

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableBoundaryDenom_lower {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10) :
    (c + 1) ^ 2 ≤ 3 * stableBoundaryDenom y ∧ c + 1 ≤ stableBoundaryDenom y := by
  obtain ⟨hK, hml, hm0, _, _, _⟩ := stable_boundary_band hc hm
  have hm2 := (sq_le_sq₀ (by positivity : 0 ≤ (5 / 8 : ℝ) * (c + 1)) hm0).mpr hml
  unfold stableBoundaryDenom
  constructor
  · nlinarith [sq_nonneg (y 1 - y 2)]
  · nlinarith [sq_nonneg (y 1 - y 2), sq_nonneg (c + 1 - 3)]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stable_scaled_entry_bound {y : StableState} {c B : ℝ} {i j : Fin 3}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10) (hB : 0 ≤ B)
    (hentry : |stableBoundaryJacobian y i j -
      stableBoundaryField y i / stableBoundaryDenom y * stableDenomGradient y j| ≤ 3 * (c + 1) * B) :
    |(c + 1) * stableOriginalJacobian y i j| ≤ 64 * B := by
  have hK : 0 < c + 1 := by linarith
  have hD := stableBoundaryDenom_pos y
  have hscale : 6 * (c + 1) ^ 2 / stableBoundaryDenom y ≤ 18 := by
    apply (div_le_iff₀ hD).mpr
    nlinarith [(stableBoundaryDenom_lower hc hm).1]
  rw [stableOriginalJacobian_factor, abs_mul, abs_of_pos hK, abs_mul,
    abs_of_pos (by positivity : 0 < 6 / stableBoundaryDenom y)]
  calc
    _ ≤ (c + 1) * (6 / stableBoundaryDenom y * (3 * (c + 1) * B)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hentry (by positivity)) hK.le
    _ = (6 * (c + 1) ^ 2 / stableBoundaryDenom y) * (3 * B) := by ring
    _ ≤ 18 * (3 * B) := mul_le_mul_of_nonneg_right hscale (by positivity)
    _ ≤ 64 * B := by linarith

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableRescaledJacobian_center_column {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) :
    |(c + 1) * stableOriginalJacobian y 1 0| ≤ 64 * |y 1| ∧
    |(c + 1) * stableOriginalJacobian y 2 0| ≤ 64 * |y 2| := by
  obtain ⟨hK, _, hm0, hmK, _, _⟩ := stable_boundary_band hc hm
  have H := stableBoundary_field_div_bounds hc hm hu hw
  have hg : |stableDenomGradient y 0| ≤ 2 * (c + 1) := by
    change |2 * y 0| ≤ _
    rw [abs_of_nonneg (by positivity)]
    linarith
  constructor
  · apply stable_scaled_entry_bound hc hm (abs_nonneg _)
    have hf : |stableBoundaryField y 1 / stableBoundaryDenom y * stableDenomGradient y 0| ≤
        2 * (c + 1) * |y 1| := by
      rw [abs_mul]
      nlinarith [mul_le_mul H.1 hg (abs_nonneg _) (abs_nonneg _)]
    have hp : |stableBoundaryJacobian y 1 0| ≤ (c + 1) * |y 1| := by
      change |-y 0 * y 1| ≤ _
      rw [abs_mul, abs_neg, abs_of_nonneg hm0]
      exact mul_le_mul_of_nonneg_right hmK (abs_nonneg _)
    have H' := abs_sub (stableBoundaryJacobian y 1 0)
      (stableBoundaryField y 1 / stableBoundaryDenom y * stableDenomGradient y 0)
    linarith
  · apply stable_scaled_entry_bound hc hm (abs_nonneg _)
    have hf : |stableBoundaryField y 2 / stableBoundaryDenom y * stableDenomGradient y 0| ≤
        2 * (c + 1) * |y 2| := by
      rw [abs_mul]
      nlinarith [mul_le_mul H.2 hg (abs_nonneg _) (abs_nonneg _)]
    have hp : |stableBoundaryJacobian y 2 0| ≤ (c + 1) * |y 2| := by
      change |-y 2| ≤ _
      rw [abs_neg]
      nlinarith [abs_nonneg (y 2)]
    have H' := abs_sub (stableBoundaryJacobian y 2 0)
      (stableBoundaryField y 2 / stableBoundaryDenom y * stableDenomGradient y 0)
    linarith

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableRescaledFlow_wall_decay {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) :
    |stableRescaledFlow (c + 1) y s 1| ≤ |y 1| * Real.exp (-3 * (c + 1) / 8 * s) ∧
    |stableRescaledFlow (c + 1) y s 2| ≤ |y 2| * Real.exp (-(3 / 4) * s) := by
  let x := fromProjectiveState (stableBoundaryEntry (y 0) (y 1) (y 2))
  let Y := stableBoundaryOrbit (y 0) (y 1) (y 2)
  let z := normalizedStableClock x 0 0 c
  have hK : 0 < c + 1 := by linarith
  have ht : 0 ≤ (c + 1) * s := mul_nonneg hK.le hs
  have hx : stateConstraint x = 1 :=
    fromProjectiveState_constraint (ne_of_gt (stableBoundaryEntry_denom_pos (y 0) (y 1) (y 2)))
  have hg := stableBoundaryOrbit_global hc hm hu hw
  have hdec := (normalized_stable_prefix_estimates hx hc (le_refl 0) ht
    (fun r hr => lt_of_lt_of_le (by positivity : 0 < 3 / (c + 1) ^ 2) (hg r hr.1).1)
    (fun r hr => (hg r hr.1).2.1)).2.1 ((c + 1) * s) ⟨ht, le_rfl⟩
  have hz : 3 * s ≤ z ((c + 1) * s) := by
    have H := normalizedStableClock_lower hx hc (le_refl 0) ht (fun r hr => (hg r hr.1).1)
    convert! H using 1
    simp only [sub_zero]
    field_simp
  have hU : |Y ((c + 1) * s) 1| ≤ |y 1| * Real.exp (-(c + 1) / 8 * z ((c + 1) * s)) := by
    have H := hdec.1
    change |Y ((c + 1) * s) 1| ≤ |Y 0 1| * Real.exp (-(c + 1) / 8 * z ((c + 1) * s)) at H
    simpa [Y, stableBoundaryOrbit_initial, stableBoundaryEntry] using H
  have hW : |Y ((c + 1) * s) 3| ≤ |y 2| * Real.exp (-(1 / 4) * z ((c + 1) * s)) := by
    have H := hdec.2
    change |Y ((c + 1) * s) 3| ≤ |Y 0 3| * Real.exp (-(1 / 4) * z ((c + 1) * s)) at H
    simpa [Y, stableBoundaryOrbit_initial, stableBoundaryEntry] using H
  simp only [stableRescaledFlow, stableOriginalFlow_eq, stableRestriction_apply]
  constructor
  · exact hU.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (by nlinarith [mul_le_mul_of_nonneg_left hz hK.le])) (abs_nonneg _))
  · exact hW.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (abs_nonneg _))

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableRescaledFlow_amplitude_decay {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) :
    |stableRescaledFlow (c + 1) y s 1| + |stableRescaledFlow (c + 1) y s 2| ≤
      (|y 1| + |y 2|) * Real.exp (-s / 2) := by
  have H := stableRescaledFlow_wall_decay hc hm hu hw hs
  have hU : Real.exp (-3 * (c + 1) / 8 * s) ≤ Real.exp (-s / 2) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hW : Real.exp (-(3 / 4) * s) ≤ Real.exp (-s / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  have H' := add_le_add (H.1.trans (mul_le_mul_of_nonneg_left hU (abs_nonneg _)))
    (H.2.trans (mul_le_mul_of_nonneg_left hW (abs_nonneg _)))
  nlinarith only [H']

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableDenomGradient_wall_bound (y : StableState) (j : Fin 3) (hj : j ≠ 0) :
    |stableDenomGradient y j| ≤ 2 * (|y 1| + |y 2|) := by
  fin_cases j
  · exact (hj rfl).elim
  · change |2 * (y 1 - y 2)| ≤ _
    rw [abs_mul]
    norm_num only
    exact mul_le_mul_of_nonneg_left (abs_sub _ _) (by norm_num)
  · change |2 * (y 2 - y 1)| ≤ _
    rw [abs_mul]
    norm_num only
    have H := abs_sub (y 2) (y 1)
    linarith

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableDenomGradient_bound {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) (v : StableState) :
    |dotProduct (stableDenomGradient y) v| ≤ 6 * (c + 1) * ‖v‖ := by
  obtain ⟨hK, _, hm0, hmK, _, _⟩ := stable_boundary_band hc hm
  have hg (j : Fin 3) : |stableDenomGradient y j| ≤ 2 * (c + 1) := by
    by_cases hj : j = 0
    · subst j
      change |2 * y 0| ≤ _
      rw [abs_of_nonneg (by positivity)]
      linarith
    · exact (stableDenomGradient_wall_bound y j hj).trans (by linarith)
  have hv (j : Fin 3) : |v j| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v j
  have hprod (j : Fin 3) : |stableDenomGradient y j * v j| ≤ 2 * (c + 1) * ‖v‖ := by
    rw [abs_mul]
    exact mul_le_mul (hg j) (hv j) (abs_nonneg _) (by positivity)
  calc
    _ ≤ ∑ j, |stableDenomGradient y j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin 3, 2 * (c + 1) * ‖v‖ := Finset.sum_le_sum (fun j _ => hprod j)
    _ = _ := by simp; ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableDenomHessian_bound (v w : StableState) :
    |stableDenomHessian v w| ≤ 10 * ‖v‖ * ‖w‖ := by
  have hv (j : Fin 3) : |v j| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v j
  have hw (j : Fin 3) : |w j| ≤ ‖w‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm w j
  have hvd : |v 1 - v 2| ≤ 2 * ‖v‖ := (abs_sub _ _).trans (by linarith [hv 1, hv 2])
  have hwd : |w 1 - w 2| ≤ 2 * ‖w‖ := (abs_sub _ _).trans (by linarith [hw 1, hw 2])
  have H0 := mul_le_mul (hv 0) (hw 0) (abs_nonneg _) (norm_nonneg _)
  have H1 := mul_le_mul hvd hwd (abs_nonneg _) (by positivity)
  have H := abs_add_le (2 * v 0 * w 0) (2 * (v 1 - v 2) * (w 1 - w 2))
  simp only [abs_mul] at H
  norm_num only at H
  change |stableDenomHessian v w| ≤ _ at H
  nlinarith only [H, H0, H1]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.stableRescaledJacobian_signedRowSum {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) (i : Fin 3) :
    signedRowSum ((c + 1) • stableOriginalJacobian y) i ≤ 256 * (|y 1| + |y 2|) := by
  have hK : 0 < c + 1 := by linarith
  have hb : 0 ≤ |y 1| + |y 2| := by positivity
  have hb1 : |y 1| + |y 2| ≤ 1 := by linarith
  have hb2 : (|y 1| + |y 2|) ^ 2 ≤ |y 1| + |y 2| := by nlinarith
  have H := stableRescaledJacobian_center_bounds hc hm hu hw
  have C := stableRescaledJacobian_center_column hc hm hu hw
  have S := stableRescaledJacobian_stable_rows hc hm hu hw
  simp only [abs_mul, abs_of_pos hK] at H C
  have hfin : Finset.univ = ({0, 1, 2} : Finset (Fin 3)) := by decide
  fin_cases i
  · simp [signedRowSum, hfin, Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hK]
    have hd := mul_le_mul_of_nonneg_left (le_abs_self (stableOriginalJacobian y 0 0)) hK.le
    nlinarith only [H.1, H.2.1, H.2.2, hd, hb2, hb]
  · simp [signedRowSum, hfin, Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hK]
    nlinarith only [S.1, C.1, hc, abs_nonneg (y 1), abs_nonneg (y 2)]
  · simp [signedRowSum, hfin, Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hK]
    nlinarith only [S.2, C.2, abs_nonneg (y 1), abs_nonneg (y 2)]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.stableRescaledDifferential_bound {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) (v : StableState) :
    ‖stableRescaledDifferential (c + 1) y s v‖ ≤
      Real.exp (512 * (|y 1| + |y 2|)) * ‖v‖ := by
  let b := |y 1| + |y 2|
  let J := fun r => stableRescaledDifferential (c + 1) y r v
  let A := fun r => (c + 1) • stableOriginalJacobian (stableRescaledFlow (c + 1) y r)
  let z := fun r => 512 * b * (1 - Real.exp (-r / 2))
  have hK : 0 < c + 1 := by linarith
  have hJ (r : ℝ) (hr : r ∈ Icc 0 s) : HasDerivAt J ((A r).mulVec (J r)) r := by
    simpa only [A, Matrix.smul_mulVec] using
      stableRescaledFlow_variational_equation hK hc hm hu hw hr.1 v
  have hz (r : ℝ) : HasDerivAt z (256 * b * Real.exp (-r / 2)) r := by
    convert! ((hasDerivAt_const r (1 : ℝ)).sub (((hasDerivAt_id r).neg.div_const 2).exp)).const_mul
      (512 * b) using 1
    dsimp
    ring
  have hrow (r : ℝ) (hr : r ∈ Ico 0 s) (i : Fin 3) :
      signedRowSum (A r) i ≤ 256 * b * Real.exp (-r / 2) := by
    obtain ⟨hm', hu', hw'⟩ := stableRescaledFlow_band hc hm hu hw hr.1
    have H := stableRescaledJacobian_signedRowSum hc hm' hu' hw' i
    have H' := mul_le_mul_of_nonneg_left (stableRescaledFlow_amplitude_decay hc hm hu hw hr.1)
      (by norm_num : (0 : ℝ) ≤ 256)
    exact H.trans (by nlinarith only [H'])
  have H := norm_le_exp_of_signedRowSum (HasDerivAt.continuousOn hJ)
    (fun r hr => hJ r (Ico_subset_Icc_self hr))
    (HasDerivAt.continuousOn (fun r _ => hz r)) (fun r _ => hz r) hrow s ⟨hs, le_rfl⟩
  have hzero : J 0 = v := by simp only [J, stableRescaledDifferential_initial, ContinuousLinearMap.id_apply]
  have hz0 : z 0 = 0 := by simp [z]
  rw [hzero, hz0, sub_zero] at H
  have hzb : z s ≤ 512 * b := by
    have hb : 0 ≤ b := by dsimp [b]; positivity
    dsimp [z]
    nlinarith [Real.exp_pos (-s / 2)]
  have H' := H.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hzb) (norm_nonneg v))
  simpa only [mul_comm] using H'

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableTangent_split_bounds (v : StableState) :
    ‖(![v 0, 0, 0] : StableState)‖ ≤ ‖v‖ ∧
      ‖(![0, v 1, v 2] : StableState)‖ ≤ ‖![v 1, v 2]‖ ∧ ‖![v 1, v 2]‖ ≤ ‖v‖ := by
  constructor
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
    intro i
    fin_cases i
    · exact norm_le_pi_norm v 0
    · simp
    · simp
  constructor
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    fin_cases i
    · simp
    · exact norm_le_pi_norm ![v 1, v 2] 0
    · exact norm_le_pi_norm ![v 1, v 2] 1
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
    intro i
    fin_cases i
    · exact norm_le_pi_norm v 1
    · exact norm_le_pi_norm v 2

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiff_stableResidualClock (n : WithTop ℕ∞) (K : ℝ) :
    ContDiff ℝ n (stableResidualClock K) := by
  unfold stableResidualClock
  exact contDiff_const.div (contDiff_stableBoundaryDenom n) (fun y => (stableBoundaryDenom_pos y).ne')

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_stableResidualClock {gamma : ℝ → StableState} {v : StableState} {t : ℝ}
    (h : HasDerivAt gamma v t) (K : ℝ) :
    HasDerivAt (fun s => stableResidualClock K (gamma s))
      (-(6 * K / stableBoundaryDenom (gamma t) ^ 2) * dotProduct (stableDenomGradient (gamma t)) v) t := by
  have H := (hasDerivAt_const t (6 * K)).div (hasDerivAt_stableBoundaryDenom h)
    (stableBoundaryDenom_pos (gamma t)).ne'
  convert! H using 1
  simp
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableResidualClock_fderiv (K : ℝ) (y v : StableState) :
    fderiv ℝ (stableResidualClock K) y v =
      -(6 * K / stableBoundaryDenom y ^ 2) * dotProduct (stableDenomGradient y) v := by
  have hl : HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1
    simp
  have hd := ((contDiff_stableResidualClock 1 K).differentiable (by norm_num) y).hasFDerivAt
  have H := (show HasFDerivAt (stableResidualClock K) (fderiv ℝ (stableResidualClock K) y)
      (y + (0 : ℝ) • v) by simpa using hd).comp_hasDerivAt 0 hl
  simpa only [zero_smul, add_zero] using H.unique (hasDerivAt_stableResidualClock hl K)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableResidualClock_fderiv2 (K : ℝ) (y v w : StableState) :
    fderiv ℝ (fderiv ℝ (stableResidualClock K)) y v w =
      stableResidualClock K y *
        (2 * (dotProduct (stableDenomGradient y) v / stableBoundaryDenom y) *
          (dotProduct (stableDenomGradient y) w / stableBoundaryDenom y) -
          stableDenomHessian v w / stableBoundaryDenom y) := by
  have hl : HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1
    simp
  have hd := ((contDiff_stableResidualClock 2 K).fderiv_right
    (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable (by norm_num)
  have Hleft := hasDerivAt_fderiv_apply_const (hd (y + (0 : ℝ) • v)) hl w
  simp only [stableResidualClock_fderiv] at Hleft
  have hD := hasDerivAt_stableBoundaryDenom hl
  have hG := hasDerivAt_stableDenomGradient_dotProduct hl w
  have Hright := (((hasDerivAt_const (0 : ℝ) (6 * K)).div (hD.pow 2)
    (pow_ne_zero 2 (stableBoundaryDenom_pos _).ne')).neg).mul hG
  have H := Hleft.unique Hright
  simp only [Pi.pow_apply, Pi.div_apply, Pi.neg_apply, zero_smul, add_zero] at H
  rw [H]
  unfold stableResidualClock
  have hn := (stableBoundaryDenom_pos y).ne'
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableResidualClock_bound {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10) :
    |stableResidualClock (c + 1) y| ≤ 18 / (c + 1) := by
  have hK : 0 < c + 1 := by linarith
  have hD := stableBoundaryDenom_pos y
  rw [stableResidualClock, abs_of_pos (by positivity)]
  apply (div_le_div_iff₀ hD hK).mpr
  nlinarith [(stableBoundaryDenom_lower hc hm).1]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableDenomGradient_ratio_bound {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) (v : StableState) :
    |dotProduct (stableDenomGradient y) v / stableBoundaryDenom y| ≤ 6 * ‖v‖ := by
  rw [abs_div, abs_of_pos (stableBoundaryDenom_pos y)]
  apply (div_le_iff₀ (stableBoundaryDenom_pos y)).mpr
  have H := mul_le_mul_of_nonneg_right (stableBoundaryDenom_lower hc hm).2 (show 0 ≤ 6 * ‖v‖ by positivity)
  nlinarith only [H, stableDenomGradient_bound hc hm hu hw v]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableResidualClock_first_bound {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) (v : StableState) :
    |fderiv ℝ (stableResidualClock (c + 1)) y v| ≤ 108 / (c + 1) * ‖v‖ := by
  have hK : 0 < c + 1 := by linarith
  rw [stableResidualClock_fderiv]
  have heq : -(6 * (c + 1) / stableBoundaryDenom y ^ 2) * dotProduct (stableDenomGradient y) v =
      -stableResidualClock (c + 1) y * (dotProduct (stableDenomGradient y) v / stableBoundaryDenom y) := by
    unfold stableResidualClock
    ring
  rw [heq, abs_mul, abs_neg]
  have H := mul_le_mul (stableResidualClock_bound hc hm) (stableDenomGradient_ratio_bound hc hm hu hw v)
    (abs_nonneg _) (by positivity : 0 ≤ 18 / (c + 1))
  convert! H using 1
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableResidualClock_second_bound {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) (v w : StableState) :
    |fderiv ℝ (fderiv ℝ (stableResidualClock (c + 1))) y v w| ≤ 1476 / (c + 1) * ‖v‖ * ‖w‖ := by
  have hK : 0 < c + 1 := by linarith
  have hD := stableBoundaryDenom_pos y
  have hD1 : 1 ≤ stableBoundaryDenom y := by
    have H := (stableBoundaryDenom_lower hc hm).2
    linarith
  have H1 := mul_le_mul (stableDenomGradient_ratio_bound hc hm hu hw v)
    (stableDenomGradient_ratio_bound hc hm hu hw w) (abs_nonneg _) (by positivity : 0 ≤ 6 * ‖v‖)
  have H2 : |stableDenomHessian v w / stableBoundaryDenom y| ≤ 10 * ‖v‖ * ‖w‖ := by
    rw [abs_div, abs_of_pos hD]
    apply (div_le_iff₀ hD).mpr
    have H := mul_le_mul_of_nonneg_left hD1 (show 0 ≤ 10 * ‖v‖ * ‖w‖ by positivity)
    nlinarith only [H, stableDenomHessian_bound v w]
  have H3 : |2 * (dotProduct (stableDenomGradient y) v / stableBoundaryDenom y) *
      (dotProduct (stableDenomGradient y) w / stableBoundaryDenom y) -
      stableDenomHessian v w / stableBoundaryDenom y| ≤ 82 * ‖v‖ * ‖w‖ := by
    have H := abs_sub (2 * (dotProduct (stableDenomGradient y) v / stableBoundaryDenom y) *
      (dotProduct (stableDenomGradient y) w / stableBoundaryDenom y)) (stableDenomHessian v w / stableBoundaryDenom y)
    simp only [abs_mul] at H
    norm_num only at H
    nlinarith only [H, H1, H2]
  rw [stableResidualClock_fderiv2, abs_mul]
  have H := mul_le_mul (stableResidualClock_bound hc hm) H3 (abs_nonneg _) (by positivity : 0 ≤ 18 / (c + 1))
  convert! H using 1
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableResidualClock_derivative_bounds {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) :
    |stableResidualClock (c + 1) y| ≤ 1500 / (c + 1) ∧
      ‖fderiv ℝ (stableResidualClock (c + 1)) y‖ ≤ 1500 / (c + 1) ∧
      ‖fderiv ℝ (fderiv ℝ (stableResidualClock (c + 1))) y‖ ≤ 1500 / (c + 1) := by
  have hK : 0 < c + 1 := by linarith
  refine ⟨(stableResidualClock_bound hc hm).trans (div_le_div_of_nonneg_right (by norm_num) hK.le), ?_, ?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    exact (stableResidualClock_first_bound hc hm hu hw v).trans
      (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (by norm_num) hK.le) (norm_nonneg v))
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro w
    exact (stableResidualClock_second_bound hc hm hu hw v w).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (by norm_num) hK.le) (norm_nonneg v)) (norm_nonneg w))

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableCenterWeakProjection_apply (y : StableState) :
    stableCenterWeakProjection y = ![y 0, y 2] := by ext i; fin_cases i <;> rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableCenterWeakProjection_norm : ‖stableCenterWeakProjection‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro y
  rw [one_mul, stableCenterWeakProjection_apply]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg y)).mpr
  intro i; fin_cases i
  · exact norm_le_pi_norm y 0
  · exact norm_le_pi_norm y 2

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exists_stableScaledResidualCoefficient_bounds :
    ∃ C > (0 : ℝ), ∀ (c : ℝ) (y : StableState), 2 ≤ c → |y 0 - c| ≤ 1 / 10 →
      |y 1| ≤ 1 / 100 → |y 2| ≤ 1 / 100 → ∀ i : Fin 4,
      ContDiffAt ℝ 2 (stableScaledResidualCoefficient (c + 1) i) y ∧
        |stableScaledResidualCoefficient (c + 1) i y| ≤ C / (c + 1) ^ 2 ∧
        ‖fderiv ℝ (stableScaledResidualCoefficient (c + 1) i) y‖ ≤ C / (c + 1) ^ 2 ∧
        ‖fderiv ℝ (fderiv ℝ (stableScaledResidualCoefficient (c + 1) i)) y‖ ≤ C / (c + 1) ^ 2 := by
  obtain ⟨C, hC, HC⟩ := exists_stableResidualCoefficient_band_derivative_bounds
  refine ⟨6000 * C, by positivity, ?_⟩
  intro c y hc hm hu hw i
  have hK : 0 < c + 1 := by linarith
  have hmw : |stableCenterWeakProjection y 0 - c| ≤ 1 / 10 := hm
  have hww : |stableCenterWeakProjection y 1| ≤ 1 := by change |y 2| ≤ 1; linarith
  obtain ⟨hg, hg0, hg1, hg2⟩ := HC c (stableCenterWeakProjection y) hc hmw hww i
  have hpre := clm_precomp_second_derivative_bounds stableCenterWeakProjection stableCenterWeakProjection_norm
    (by positivity : 0 ≤ C / (c + 1)) hg hg1 hg2
  have hcomp : ContDiffAt ℝ 2 (stableResidualCoefficient i ∘ stableCenterWeakProjection) y :=
    hg.comp y stableCenterWeakProjection.contDiff.contDiffAt
  obtain ⟨hq0, hq1, hq2⟩ := stableResidualClock_derivative_bounds hc hm hu hw
  have hreg : ContDiffAt ℝ 2 (stableResidualClock (c + 1)) y :=
    (contDiff_stableResidualClock 2 (c + 1)).contDiffAt
  obtain ⟨H0, H1, H2⟩ := product_second_derivative_bounds hreg hcomp
    (by positivity : 0 ≤ 1500 / (c + 1)) (by positivity : 0 ≤ C / (c + 1))
    hq0 hq1 hq2 hg0 hpre.1 hpre.2
  have hsame : stableScaledResidualCoefficient (c + 1) i =
      (fun z => stableResidualClock (c + 1) z * (stableResidualCoefficient i ∘ stableCenterWeakProjection) z) := rfl
  rw [hsame]
  refine ⟨hreg.mul hcomp, ?_⟩
  have hnonneg : 0 ≤ C / (c + 1) ^ 2 := by positivity
  simp only [div_eq_mul_inv, ← inv_pow] at H0 H1 H2 hnonneg ⊢
  exact ⟨by nlinarith only [H0, hnonneg], by nlinarith only [H1, hnonneg], by nlinarith only [H2]⟩

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableCubicFirstBudget_nonneg (y v : StableState) : 0 ≤ stableCubicFirstBudget y v := by
  unfold stableCubicFirstBudget
  positivity

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableCubicSecondBudget_nonneg (y v w : StableState) : 0 ≤ stableCubicSecondBudget y v w := by
  unfold stableCubicSecondBudget
  positivity

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableScaledResidual_factor (K : ℝ) (y : StableState) :
    stableScaledResidual K y = y 1 * stableScaledResidualCubic K y := by
  simp [stableScaledResidual, stableScaledResidualCubic, stableScaledResidualCoefficient,
    stableResidualCoefficient, stableCenterWeakProjection_apply, stableCubicMonomial,
    stableCorrectedResidual, Fin.sum_univ_succ]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exists_stableScaledResidualCubic_bounds :
    ∃ C > (0 : ℝ), ∀ (c : ℝ) (y : StableState), 2 ≤ c → |y 0 - c| ≤ 1 / 10 →
      |y 1| ≤ 1 / 100 → |y 2| ≤ 1 / 100 →
      ContDiffAt ℝ 2 (stableScaledResidualCubic (c + 1)) y ∧
        |stableScaledResidualCubic (c + 1) y| ≤ C / (c + 1) ^ 2 * (|y 1| + |y 2|) ^ 3 ∧
        (∀ v, |fderiv ℝ (stableScaledResidualCubic (c + 1)) y v| ≤ C / (c + 1) ^ 2 * stableCubicFirstBudget y v) ∧
        (∀ v w, |fderiv ℝ (fderiv ℝ (stableScaledResidualCubic (c + 1))) y v w| ≤ C / (c + 1) ^ 2 * stableCubicSecondBudget y v w) := by
  obtain ⟨C, hC, HC⟩ := exists_stableScaledResidualCoefficient_bounds
  refine ⟨4 * C, by positivity, ?_⟩
  intro c y hc hm hu hw
  have H := stableScaledResidualCubic_bounds_of_coefficients (by positivity : 0 ≤ C / (c + 1) ^ 2) (HC c y hc hm hu hw)
  have hscale : 4 * (C / (c + 1) ^ 2) = 4 * C / (c + 1) ^ 2 := by ring
  simpa only [hscale] using H

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.isOpen_stableParameterDomain (c : ℝ) : IsOpen (stableParameterDomain c) :=
  (isOpen_lt ((continuous_apply 0).sub continuous_const).abs continuous_const).inter
    ((isOpen_lt (continuous_apply 1).abs continuous_const).inter
      (isOpen_lt (continuous_apply 2).abs continuous_const))

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableStrongHessianBudget_nonneg (y v w : StableState) :
    0 ≤ stableStrongHessianBudget y v w := by unfold stableStrongHessianBudget; positivity

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableFirstInputWeight_nonneg {b : ℝ} (hb : 0 ≤ b) (v : StableState) :
    0 ≤ stableFirstInputWeight b v := by unfold stableFirstInputWeight; positivity

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableSecondInputWeight_nonneg {b : ℝ} (hb : 0 ≤ b) (v w : StableState) :
    0 ≤ stableSecondInputWeight b v w := by unfold stableSecondInputWeight; positivity

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableSecondInputWeight_product (b : ℝ) (v w : StableState) :
    b * stableSecondInputWeight b v w ≤ stableFirstInputWeight b v * stableFirstInputWeight b w := by
  unfold stableSecondInputWeight stableFirstInputWeight
  nlinarith only [mul_nonneg (norm_nonneg (![v 1, v 2] : Fin 2 → ℝ))
    (norm_nonneg (![w 1, w 2] : Fin 2 → ℝ))]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableCubicFirstBudget_norm {Y a : StableState} {b : ℝ}
    (hb1 : b ≤ 1) (hY : |Y 1| + |Y 2| ≤ b) :
    stableCubicFirstBudget Y a ≤ 4 * b ^ 2 * ‖a‖ := by
  have h2 := pow_le_pow_left₀ (by positivity : 0 ≤ |Y 1| + |Y 2|) hY 2
  have h3 := pow_le_pow_left₀ (by positivity : 0 ≤ |Y 1| + |Y 2|) hY 3
  have H0 := mul_le_mul_of_nonneg_right h3 (norm_nonneg a)
  have H1 := mul_le_mul h2 (stableTangent_split_bounds a).2.2 (norm_nonneg _) (sq_nonneg b)
  have H2 := mul_le_mul_of_nonneg_right hb1 (show 0 ≤ b ^ 2 * ‖a‖ by positivity)
  unfold stableCubicFirstBudget
  nlinarith only [H0, H1, H2]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableCubicFirstBudget_weighted {Y a v : StableState} {b E : ℝ}
    (hb : 0 ≤ b) (hE : 0 ≤ E) (hY : |Y 1| + |Y 2| ≤ b)
    (ha : ‖a‖ ≤ E * ‖v‖) (haz : ‖![a 1, a 2]‖ ≤ 256 * E * stableFirstInputWeight b v) :
    stableCubicFirstBudget Y a ≤ 769 * E * b ^ 2 * stableFirstInputWeight b v := by
  have h2 := pow_le_pow_left₀ (by positivity : 0 ≤ |Y 1| + |Y 2|) hY 2
  have h3 := pow_le_pow_left₀ (by positivity : 0 ≤ |Y 1| + |Y 2|) hY 3
  have H0 := mul_le_mul h3 ha (norm_nonneg _) (by positivity : 0 ≤ b ^ 3)
  have H1 := mul_le_mul h2 haz (norm_nonneg _) (sq_nonneg b)
  have hA : b * ‖v‖ ≤ stableFirstInputWeight b v := by
    unfold stableFirstInputWeight; exact le_add_of_nonneg_right (norm_nonneg _)
  have H2 := mul_le_mul_of_nonneg_left hA (show 0 ≤ E * b ^ 2 by positivity)
  unfold stableCubicFirstBudget
  nlinarith only [H0, H1, H2]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableCubicSecondBudget_weighted {Y a d v w : StableState} {b E : ℝ}
    (hb : 0 ≤ b) (hE : 0 ≤ E) (hY : |Y 1| + |Y 2| ≤ b)
    (ha : ‖a‖ ≤ E * ‖v‖) (hd : ‖d‖ ≤ E * ‖w‖)
    (haz : ‖![a 1, a 2]‖ ≤ 256 * E * stableFirstInputWeight b v)
    (hdz : ‖![d 1, d 2]‖ ≤ 256 * E * stableFirstInputWeight b w) :
    stableCubicSecondBudget Y a d ≤
      400000 * E ^ 2 * b * stableFirstInputWeight b v * stableFirstInputWeight b w := by
  let A := stableFirstInputWeight b v
  let B := stableFirstInputWeight b w
  have hA : 0 ≤ A := stableFirstInputWeight_nonneg hb v
  have hB : 0 ≤ B := stableFirstInputWeight_nonneg hb w
  have hav : b * ‖v‖ ≤ A := by dsimp [A, stableFirstInputWeight]; exact le_add_of_nonneg_right (norm_nonneg _)
  have hbw : b * ‖w‖ ≤ B := by dsimp [B, stableFirstInputWeight]; exact le_add_of_nonneg_right (norm_nonneg _)
  have h2 := pow_le_pow_left₀ (by positivity : 0 ≤ |Y 1| + |Y 2|) hY 2
  have h3 := pow_le_pow_left₀ (by positivity : 0 ≤ |Y 1| + |Y 2|) hY 3
  have H0 := mul_le_mul (mul_le_mul h3 ha (norm_nonneg _) (by positivity : 0 ≤ b ^ 3)) hd
    (norm_nonneg _) (by positivity : 0 ≤ b ^ 3 * (E * ‖v‖))
  have H1 := mul_le_mul h2 (mul_le_mul ha hdz (norm_nonneg _) (by positivity : 0 ≤ E * ‖v‖))
    (by positivity) (sq_nonneg b)
  have H2 := mul_le_mul h2 (mul_le_mul haz hd (norm_nonneg _) (by positivity : 0 ≤ 256 * E * A))
    (by positivity) (sq_nonneg b)
  have H3 := mul_le_mul (mul_le_mul hY haz (norm_nonneg _) hb) hdz
    (norm_nonneg _) (by positivity : 0 ≤ b * (256 * E * A))
  have T0 := mul_le_mul_of_nonneg_left (mul_le_mul hav hbw (by positivity) hA)
    (show 0 ≤ E ^ 2 * b by positivity)
  have T1 := mul_le_mul_of_nonneg_left hav (show 0 ≤ E ^ 2 * b * B by positivity)
  have T2 := mul_le_mul_of_nonneg_left hbw (show 0 ≤ E ^ 2 * b * A by positivity)
  change stableCubicSecondBudget Y a d ≤ 400000 * E ^ 2 * b * A * B
  dsimp only [A, B] at H0 H1 H2 H3 T0 T1 T2 ⊢
  unfold stableCubicSecondBudget
  nlinarith only [H0, H1, H2, H3, T0, T1, T2,
    show 0 ≤ E ^ 2 * b * stableFirstInputWeight b v * stableFirstInputWeight b w from
      mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg E) hb) hA) hB]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableScaledResidual_contDiffAt {K : ℝ} {y : StableState}
    (hg : ContDiffAt ℝ 2 (stableScaledResidualCubic K) y) :
    ContDiffAt ℝ 2 (stableScaledResidual K) y := by
  have heq : stableScaledResidual K = fun z => z 1 * stableScaledResidualCubic K z :=
    funext (stableScaledResidual_factor K)
  rw [heq]
  exact (contDiffAt_apply ℝ ℝ 1 y).mul hg

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableScaledResidual_fderiv {K : ℝ} {y : StableState}
    (hg : ContDiffAt ℝ 2 (stableScaledResidualCubic K) y) (v : StableState) :
    fderiv ℝ (stableScaledResidual K) y v =
      v 1 * stableScaledResidualCubic K y + y 1 * fderiv ℝ (stableScaledResidualCubic K) y v := by
  have heq : stableScaledResidual K = fun z => z 1 * stableScaledResidualCubic K z :=
    funext (stableScaledResidual_factor K)
  rw [heq, fderiv_fun_mul ((contDiffAt_apply (n := 1) ℝ ℝ 1 y).differentiableAt (by norm_num))
    (hg.differentiableAt (by norm_num))]
  have hp : fderiv ℝ (fun z : StableState => z 1) y =
      (ContinuousLinearMap.proj 1 : StableState →L[ℝ] ℝ) :=
    (ContinuousLinearMap.proj 1 : StableState →L[ℝ] ℝ).fderiv
  rw [hp]
  change y 1 * fderiv ℝ (stableScaledResidualCubic K) y v + stableScaledResidualCubic K y * v 1 = _
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableScaledResidual_fderiv2 {K : ℝ} {y : StableState}
    (hg : ContDiffAt ℝ 2 (stableScaledResidualCubic K) y) (v w : StableState) :
    fderiv ℝ (fderiv ℝ (stableScaledResidual K)) y v w =
      v 1 * fderiv ℝ (stableScaledResidualCubic K) y w +
        w 1 * fderiv ℝ (stableScaledResidualCubic K) y v +
        y 1 * fderiv ℝ (fderiv ℝ (stableScaledResidualCubic K)) y v w := by
  have heq : stableScaledResidual K = fun z => z 1 * stableScaledResidualCubic K z :=
    funext (stableScaledResidual_factor K)
  rw [heq, fderiv2_mul_apply (contDiffAt_apply ℝ ℝ 1 y) hg]
  have hp : fderiv ℝ (fun z : StableState => z 1) =
      fun _ => (ContinuousLinearMap.proj 1 : StableState →L[ℝ] ℝ) :=
    funext (fun _ => (ContinuousLinearMap.proj 1 : StableState →L[ℝ] ℝ).fderiv)
  simp only [hp, fderiv_const_apply, zero_apply, zero_mul, add_zero]
  change y 1 * fderiv ℝ (fderiv ℝ (stableScaledResidualCubic K)) y v w +
    v 1 * fderiv ℝ (stableScaledResidualCubic K) y w +
    w 1 * fderiv ℝ (stableScaledResidualCubic K) y v = _
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableScaledResidual_bounds_of_cubic {K B : ℝ} {y : StableState}
    (hg : ContDiffAt ℝ 2 (stableScaledResidualCubic K) y)
    (h0 : |stableScaledResidualCubic K y| ≤ B * (|y 1| + |y 2|) ^ 3)
    (h1 : ∀ v, |fderiv ℝ (stableScaledResidualCubic K) y v| ≤ B * stableCubicFirstBudget y v)
    (h2 : ∀ v w, |fderiv ℝ (fderiv ℝ (stableScaledResidualCubic K)) y v w| ≤ B * stableCubicSecondBudget y v w) :
    |stableScaledResidual K y| ≤ B * |y 1| * (|y 1| + |y 2|) ^ 3 ∧
      (∀ v, |fderiv ℝ (stableScaledResidual K) y v| ≤
        B * (|v 1| * (|y 1| + |y 2|) ^ 3 + |y 1| * stableCubicFirstBudget y v)) ∧
      (∀ v w, |fderiv ℝ (fderiv ℝ (stableScaledResidual K)) y v w| ≤
        B * (|v 1| * stableCubicFirstBudget y w + |w 1| * stableCubicFirstBudget y v +
          |y 1| * stableCubicSecondBudget y v w)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [stableScaledResidual_factor, abs_mul]
    have H := mul_le_mul_of_nonneg_left h0 (abs_nonneg (y 1))
    nlinarith only [H]
  · intro v
    rw [stableScaledResidual_fderiv hg]
    have H := abs_add_le (v 1 * stableScaledResidualCubic K y)
      (y 1 * fderiv ℝ (stableScaledResidualCubic K) y v)
    simp only [abs_mul] at H
    have H0 := mul_le_mul_of_nonneg_left h0 (abs_nonneg (v 1))
    have H1 := mul_le_mul_of_nonneg_left (h1 v) (abs_nonneg (y 1))
    nlinarith only [H, H0, H1]
  · intro v w
    rw [stableScaledResidual_fderiv2 hg]
    have htri (a b c : ℝ) : |a + b + c| ≤ |a| + |b| + |c| := by
      linarith only [abs_add_le a b, abs_add_le (a + b) c]
    have H := htri (v 1 * fderiv ℝ (stableScaledResidualCubic K) y w)
      (w 1 * fderiv ℝ (stableScaledResidualCubic K) y v)
      (y 1 * fderiv ℝ (fderiv ℝ (stableScaledResidualCubic K)) y v w)
    simp only [abs_mul] at H
    have H0 := mul_le_mul_of_nonneg_left (h1 w) (abs_nonneg (v 1))
    have H1 := mul_le_mul_of_nonneg_left (h1 v) (abs_nonneg (w 1))
    have H2 := mul_le_mul_of_nonneg_left (h2 v w) (abs_nonneg (y 1))
    nlinarith only [H, H0, H1, H2]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exists_stableScaledResidual_derivative_bounds :
    ∃ C > (0 : ℝ), ∀ (c : ℝ) (y : StableState), 2 ≤ c → |y 0 - c| ≤ 1 / 10 →
      |y 1| ≤ 1 / 100 → |y 2| ≤ 1 / 100 →
      ContDiffAt ℝ 2 (stableScaledResidual (c + 1)) y ∧
        |stableScaledResidual (c + 1) y| ≤ C / (c + 1) ^ 2 * |y 1| * (|y 1| + |y 2|) ^ 3 ∧
        (∀ v, |fderiv ℝ (stableScaledResidual (c + 1)) y v| ≤
          C / (c + 1) ^ 2 * (|v 1| * (|y 1| + |y 2|) ^ 3 + |y 1| * stableCubicFirstBudget y v)) ∧
        (∀ v w, |fderiv ℝ (fderiv ℝ (stableScaledResidual (c + 1))) y v w| ≤
          C / (c + 1) ^ 2 * (|v 1| * stableCubicFirstBudget y w + |w 1| * stableCubicFirstBudget y v +
            |y 1| * stableCubicSecondBudget y v w)) := by
  obtain ⟨C, hC, HC⟩ := exists_stableScaledResidualCubic_bounds
  refine ⟨C, hC, ?_⟩
  intro c y hc hm hu hw
  obtain ⟨hg, h0, h1, h2⟩ := HC c y hc hm hu hw
  exact ⟨stableScaledResidual_contDiffAt hg,
    stableScaledResidual_bounds_of_cubic hg h0 h1 h2⟩

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.stableRescaledFlow_fderiv2 {K : ℝ} {y : StableState} {c s : ℝ}
    (hK : 0 < K) (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) (hs : 0 ≤ s) :
    fderiv ℝ (fderiv ℝ (fun z => stableRescaledFlow K z s)) y =
      stableRescaledSecondDifferential K y s := by
  have heq : fderiv ℝ (fun z => stableRescaledFlow K z s) =ᶠ[𝓝 y]
      (fun z => stableRescaledDifferential K z s) := by
    filter_upwards [(isOpen_stableParameterDomain c).mem_nhds ⟨hm, hu, hw⟩] with z hz
    exact (hasFDerivAt_stableRescaledFlow hK hc hz.1.le hz.2.1.le hz.2.2.le hs).fderiv
  rw [heq.fderiv_eq]
  exact (hasFDerivAt_stableRescaledDifferential hK hc hm.le hu.le hw.le hs).fderiv

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableRescaledDifferential_strong_budget {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) (v : StableState) :
    |stableRescaledDifferential (c + 1) y s v 1| ≤
      (|v 1| + 200 * |y 1| * Real.exp (512 * (|y 1| + |y 2|)) * ‖v‖) *
        Real.exp (-3 * (c + 1) / 16 * s) := by
  have hK : 0 < c + 1 := by linarith
  have hcoef : 512 * |y 1| * Real.exp (512 * (|y 1| + |y 2|)) * ‖v‖ / (c + 1) ≤
      200 * |y 1| * Real.exp (512 * (|y 1| + |y 2|)) * ‖v‖ := by
    apply (div_le_iff₀ hK).mpr
    nlinarith only [mul_le_mul_of_nonneg_right (show (512 : ℝ) ≤ 200 * (c + 1) by linarith)
      (show 0 ≤ |y 1| * Real.exp (512 * (|y 1| + |y 2|)) * ‖v‖ by positivity)]
  exact (stableRescaledDifferential_strong_decay hc hm hu hw hs v).trans
    (mul_le_mul_of_nonneg_right (add_le_add (le_refl _) hcoef) (Real.exp_pos _).le)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableResidualFirstDecay_bound {Y a v : StableState} {b E q : ℝ}
    (hb : 0 ≤ b) (hE : 0 ≤ E) (hq : 0 ≤ q)
    (hY : |Y 1| + |Y 2| ≤ b) (hU : |Y 1| ≤ b * q)
    (ha : ‖a‖ ≤ E * ‖v‖) (haz : ‖![a 1, a 2]‖ ≤ 256 * E * stableFirstInputWeight b v)
    (haU : |a 1| ≤ 200 * E * stableFirstInputWeight b v * q) :
    |a 1| * (|Y 1| + |Y 2|) ^ 3 + |Y 1| * stableCubicFirstBudget Y a ≤
      969 * E * b ^ 3 * stableFirstInputWeight b v * q := by
  have hA := stableFirstInputWeight_nonneg hb v
  have h3 := pow_le_pow_left₀ (by positivity : 0 ≤ |Y 1| + |Y 2|) hY 3
  have H0 := mul_le_mul haU h3 (by positivity) (by positivity : 0 ≤ 200 * E * stableFirstInputWeight b v * q)
  have H1 := mul_le_mul hU (stableCubicFirstBudget_weighted hb hE hY ha haz)
    (stableCubicFirstBudget_nonneg Y a) (mul_nonneg hb hq)
  nlinarith only [H0, H1]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableResidualSecondDecay_bound {Y a d h v w : StableState} {b E q : ℝ}
    (hb : 0 ≤ b) (hb1 : b ≤ 1) (hE : 1 ≤ E) (hq : 0 ≤ q)
    (hY : |Y 1| + |Y 2| ≤ b) (hU : |Y 1| ≤ b * q)
    (ha : ‖a‖ ≤ E * ‖v‖) (hd : ‖d‖ ≤ E * ‖w‖)
    (haz : ‖![a 1, a 2]‖ ≤ 256 * E * stableFirstInputWeight b v)
    (hdz : ‖![d 1, d 2]‖ ≤ 256 * E * stableFirstInputWeight b w)
    (haU : |a 1| ≤ 200 * E * stableFirstInputWeight b v * q)
    (hdU : |d 1| ≤ 200 * E * stableFirstInputWeight b w * q)
    (hh : ‖h‖ ≤ 2400000 * E ^ 3 * stableSecondInputWeight b v w)
    (hhU : |h 1| ≤ 320000000 * E ^ 3 * stableSecondInputWeight b v w * q) :
    |h 1| * (|Y 1| + |Y 2|) ^ 3 + |Y 1| * stableCubicFirstBudget Y h +
      |a 1| * stableCubicFirstBudget Y d + |d 1| * stableCubicFirstBudget Y a +
      |Y 1| * stableCubicSecondBudget Y a d ≤
      400000000 * E ^ 3 * b ^ 2 * stableFirstInputWeight b v * stableFirstInputWeight b w * q := by
  have hE0 : 0 ≤ E := le_trans (by norm_num) hE
  have hA := stableFirstInputWeight_nonneg hb v
  have hB := stableFirstInputWeight_nonneg hb w
  have hW := stableSecondInputWeight_nonneg hb v w
  have h3 := pow_le_pow_left₀ (by positivity : 0 ≤ |Y 1| + |Y 2|) hY 3
  have H0 := mul_le_mul hhU h3 (by positivity)
    (by positivity : 0 ≤ 320000000 * E ^ 3 * stableSecondInputWeight b v w * q)
  have Hh := (stableCubicFirstBudget_norm hb1 hY (a := h)).trans
    (mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 4 * b ^ 2))
  have H1 := mul_le_mul hU Hh (stableCubicFirstBudget_nonneg Y h) (mul_nonneg hb hq)
  have H2 := mul_le_mul haU (stableCubicFirstBudget_weighted hb hE0 hY hd hdz)
    (stableCubicFirstBudget_nonneg Y d) (by positivity : 0 ≤ 200 * E * stableFirstInputWeight b v * q)
  have H3 := mul_le_mul hdU (stableCubicFirstBudget_weighted hb hE0 hY ha haz)
    (stableCubicFirstBudget_nonneg Y a) (by positivity : 0 ≤ 200 * E * stableFirstInputWeight b w * q)
  have H4 := mul_le_mul hU (stableCubicSecondBudget_weighted hb hE0 hY ha hd haz hdz)
    (stableCubicSecondBudget_nonneg Y a d) (mul_nonneg hb hq)
  have TW := mul_le_mul_of_nonneg_left (stableSecondInputWeight_product b v w)
    (show 0 ≤ E ^ 3 * b ^ 2 * q by positivity)
  have TE := mul_le_mul_of_nonneg_right (show E ^ 2 ≤ E ^ 3 by nlinarith [sq_nonneg E])
    (show 0 ≤ b ^ 2 * stableFirstInputWeight b v * stableFirstInputWeight b w * q by positivity)
  have Tpos : 0 ≤ E ^ 3 * b ^ 2 * stableFirstInputWeight b v * stableFirstInputWeight b w * q := by positivity
  nlinarith only [H0, H1, H2, H3, H4, TW, TE, Tpos]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableRescaledResidualRate_fderiv {K c s : ℝ} {y : StableState}
    (hK : 0 < K) (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s)
    (hg : ContDiffAt ℝ 2 (stableScaledResidual K) (stableRescaledFlow K y s)) (v : StableState) :
    fderiv ℝ (stableRescaledResidualRate K s) y v =
      fderiv ℝ (stableScaledResidual K) (stableRescaledFlow K y s) (stableRescaledDifferential K y s v) := by
  exact congrArg (fun L : StableState →L[ℝ] ℝ => L v)
    (((hg.differentiableAt (by norm_num)).hasFDerivAt.comp y
      (hasFDerivAt_stableRescaledFlow hK hc hm hu hw hs)).fderiv)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableRescaledResidualRate_fderiv2 {K c s : ℝ} {y : StableState}
    (hK : 0 < K) (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) (hs : 0 ≤ s)
    (hg : ContDiffAt ℝ 2 (stableScaledResidual K) (stableRescaledFlow K y s)) (v w : StableState) :
    fderiv ℝ (fderiv ℝ (stableRescaledResidualRate K s)) y v w =
      fderiv ℝ (stableScaledResidual K) (stableRescaledFlow K y s)
        (stableRescaledSecondDifferential K y s v w) +
      fderiv ℝ (fderiv ℝ (stableScaledResidual K)) (stableRescaledFlow K y s)
        (stableRescaledDifferential K y s v) (stableRescaledDifferential K y s w) := by
  have hp : ContDiffAt ℝ 2 (fun z : StableState => (z, s)) y :=
    contDiffAt_id.prodMk contDiffAt_const
  have hf : ContDiffAt ℝ 2 (fun z => stableRescaledFlow K z s) y :=
    (contDiffAt_stableRescaledFlow_two hK hc hm.le hu.le hw.le hs).comp
      (f := fun z : StableState => (z, s)) y hp
  have H := fderiv2_comp_apply hf hg v w
  rw [stableRescaledFlow_fderiv2 hK hc hm hu hw hs,
    (hasFDerivAt_stableRescaledFlow hK hc hm.le hu.le hw.le hs).fderiv] at H
  exact H

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exists_stableRescaledResidualRate_bounds :
    ∃ C > (0 : ℝ), ∀ (c s : ℝ) (y : StableState), 2 ≤ c → |y 0 - c| < 1 / 40 →
      |y 1| < 1 / 200 → |y 2| < 1 / 200 → 0 ≤ s →
      let Y := stableRescaledFlow (c + 1) y s
      let J := stableRescaledDifferential (c + 1) y s
      let H := stableRescaledSecondDifferential (c + 1) y s
      ContDiffAt ℝ 2 (stableRescaledResidualRate (c + 1) s) y ∧
        |stableRescaledResidualRate (c + 1) s y| ≤ C / (c + 1) ^ 2 * |Y 1| * (|Y 1| + |Y 2|) ^ 3 ∧
        (∀ v, |fderiv ℝ (stableRescaledResidualRate (c + 1) s) y v| ≤
          C / (c + 1) ^ 2 * (|J v 1| * (|Y 1| + |Y 2|) ^ 3 + |Y 1| * stableCubicFirstBudget Y (J v))) ∧
        (∀ v w, |fderiv ℝ (fderiv ℝ (stableRescaledResidualRate (c + 1) s)) y v w| ≤
          C / (c + 1) ^ 2 * (|H v w 1| * (|Y 1| + |Y 2|) ^ 3 +
            |Y 1| * stableCubicFirstBudget Y (H v w) +
            |J v 1| * stableCubicFirstBudget Y (J w) +
            |J w 1| * stableCubicFirstBudget Y (J v) +
            |Y 1| * stableCubicSecondBudget Y (J v) (J w))) := by
  obtain ⟨C, hC, HC⟩ := exists_stableScaledResidual_derivative_bounds
  refine ⟨C, hC, ?_⟩
  intro c s y hc hm hu hw hs
  dsimp only
  have hK : 0 < c + 1 := by linarith
  obtain ⟨hym, hyu, hyw⟩ := stableRescaledFlow_band hc hm.le hu.le hw.le hs
  obtain ⟨hg, h0, h1, h2⟩ := HC c (stableRescaledFlow (c + 1) y s) hc hym hyu hyw
  have hp : ContDiffAt ℝ 2 (fun z : StableState => (z, s)) y :=
    contDiffAt_id.prodMk contDiffAt_const
  have hf : ContDiffAt ℝ 2 (fun z => stableRescaledFlow (c + 1) z s) y :=
    (contDiffAt_stableRescaledFlow_two hK hc hm.le hu.le hw.le hs).comp
      (f := fun z : StableState => (z, s)) y hp
  refine ⟨hg.comp y hf, h0, ?_, ?_⟩
  · intro v
    rw [stableRescaledResidualRate_fderiv hK hc hm.le hu.le hw.le hs hg]
    exact h1 _
  · intro v w
    rw [stableRescaledResidualRate_fderiv2 hK hc hm hu hw hs hg]
    have H1 := h1 (stableRescaledSecondDifferential (c + 1) y s v w)
    have H2 := h2 (stableRescaledDifferential (c + 1) y s v) (stableRescaledDifferential (c + 1) y s w)
    have H := abs_add_le
      (fderiv ℝ (stableScaledResidual (c + 1)) (stableRescaledFlow (c + 1) y s)
        (stableRescaledSecondDifferential (c + 1) y s v w))
      (fderiv ℝ (fderiv ℝ (stableScaledResidual (c + 1))) (stableRescaledFlow (c + 1) y s)
        (stableRescaledDifferential (c + 1) y s v) (stableRescaledDifferential (c + 1) y s w))
    nlinarith only [H, H1, H2]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableRescaledDifferential_stable_centerInput {y v : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s)
    (hv1 : v 1 = 0) (hv2 : v 2 = 0) :
    ‖![stableRescaledDifferential (c + 1) y s v 1, stableRescaledDifferential (c + 1) y s v 2]‖ ≤
      256 * (|y 1| + |y 2|) * Real.exp (512 * (|y 1| + |y 2|)) * ‖v‖ * Real.exp (-s / 4) := by
  have hz : (![v 1, v 2] : Fin 2 → ℝ) = 0 := by ext i; fin_cases i <;> simp [hv1, hv2]
  simpa only [hz, norm_zero, zero_add] using
    stableRescaledDifferential_stable_decay hc hm hu hw hs v

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableSecondForcing_centerInputs {y v w : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s)
    (hv1 : v 1 = 0) (hv2 : v 2 = 0) (hw1 : w 1 = 0) (hw2 : w 2 = 0) :
    ‖(c + 1) • stableOriginalHessian (stableRescaledFlow (c + 1) y s)
        (stableRescaledDifferential (c + 1) y s v) (stableRescaledDifferential (c + 1) y s w)‖ ≤
      600000 * (|y 1| + |y 2|) * Real.exp (512 * (|y 1| + |y 2|)) ^ 2 * ‖v‖ * ‖w‖ * Real.exp (-s / 4) := by
  let b := |y 1| + |y 2|
  let E := Real.exp (512 * b)
  let Jv := stableRescaledDifferential (c + 1) y s v
  let Jw := stableRescaledDifferential (c + 1) y s w
  let Y := stableRescaledFlow (c + 1) y s
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hJv := stableRescaledDifferential_bound hc hm hu hw hs v
  have hJw := stableRescaledDifferential_bound hc hm hu hw hs w
  have hZv := stableRescaledDifferential_stable_centerInput hc hm hu hw hs hv1 hv2
  have hZw := stableRescaledDifferential_stable_centerInput hc hm hu hw hs hw1 hw2
  have hbdec : |Y 1| + |Y 2| ≤ b * Real.exp (-s / 4) :=
    (stableRescaledFlow_amplitude_decay hc hm hu hw hs).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith : -s / 2 ≤ -s / 4)) hb)
  have H0 := mul_le_mul (mul_le_mul hbdec hJv (norm_nonneg _) (by positivity))
    hJw (norm_nonneg _) (by positivity)
  have H1 := mul_le_mul hZv hJw (norm_nonneg _) (by positivity)
  have H2 := mul_le_mul hJv hZw (norm_nonneg _) (by positivity)
  obtain ⟨hm', hu', hw'⟩ := stableRescaledFlow_band hc hm hu hw hs
  have H := stableRescaledHessian_bound hc hm' hu' hw' Jv Jw
  dsimp only [stableHessianBudget] at H
  change ‖(c + 1) • stableOriginalHessian Y Jv Jw‖ ≤
    600000 * b * E ^ 2 * ‖v‖ * ‖w‖ * Real.exp (-s / 4)
  have hn : 0 ≤ b * E ^ 2 * ‖v‖ * ‖w‖ * Real.exp (-s / 4) := by positivity
  nlinarith only [H, H0, H1, H2, hn]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.stableRescaledSecondDifferential_centerInputs_bound {y v w : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) (hs : 0 ≤ s)
    (hv1 : v 1 = 0) (hv2 : v 2 = 0) (hw1 : w 1 = 0) (hw2 : w 2 = 0) :
    ‖stableRescaledSecondDifferential (c + 1) y s v w‖ ≤
      2400000 * (|y 1| + |y 2|) * Real.exp (512 * (|y 1| + |y 2|)) ^ 3 * ‖v‖ * ‖w‖ := by
  have H := stableRescaledSecondDifferential_bound_of_forcing hc hm hu hw hs
    (show 0 ≤ 600000 * (|y 1| + |y 2|) * Real.exp (512 * (|y 1| + |y 2|)) ^ 2 * ‖v‖ * ‖w‖ by positivity)
    (fun r hr => stableSecondForcing_centerInputs hc hm.le hu.le hw.le hr.1 hv1 hv2 hw1 hw2)
  convert! H using 1
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableRescaledSecondDifferential_input_bound {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) (hs : 0 ≤ s) (v w : StableState) :
    ‖stableRescaledSecondDifferential (c + 1) y s v w‖ ≤
      2400000 * Real.exp (512 * (|y 1| + |y 2|)) ^ 3 * stableSecondInputWeight (|y 1| + |y 2|) v w := by
  let vc : StableState := ![v 0, 0, 0]
  let vz : StableState := ![0, v 1, v 2]
  let wc : StableState := ![w 0, 0, 0]
  let wz : StableState := ![0, w 1, w 2]
  let H := stableRescaledSecondDifferential (c + 1) y s
  have hvsum : vc + vz = v := by ext i; fin_cases i <;> simp [vc, vz]
  have hwsum : wc + wz = w := by ext i; fin_cases i <;> simp [wc, wz]
  have hv := stableTangent_split_bounds v
  have hw' := stableTangent_split_bounds w
  have hdecomp : H v w = H vc wc + H vz w + H vc wz := by
    have Hv : H v w = H vc w + H vz w := by rw [← hvsum, map_add, add_apply]
    have Hw : H vc w = H vc wc + H vc wz := by rw [← hwsum, map_add]
    rw [Hv, Hw]
    abel
  have H0 := (stableRescaledSecondDifferential_centerInputs_bound hc hm hu hw hs
    (v := vc) (w := wc) rfl rfl rfl rfl).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left hv.1 (by positivity)) hw'.1 (norm_nonneg _) (by positivity))
  have H1 := (stableRescaledSecondDifferential_bound hc hm hu hw hs vz w).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv.2.1 (by positivity)) (norm_nonneg w))
  have H2 := (stableRescaledSecondDifferential_bound hc hm hu hw hs vc wz).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left hv.1 (by positivity)) hw'.2.1 (norm_nonneg _) (by positivity))
  change ‖H v w‖ ≤ _
  rw [hdecomp]
  have Htri := (norm_add_le (H vc wc + H vz w) (H vc wz)).trans
    (add_le_add (norm_add_le _ _) (le_refl _))
  have hcross : 0 ≤ Real.exp (512 * (|y 1| + |y 2|)) ^ 3 *
      (‖![v 1, v 2]‖ * ‖w‖ + ‖v‖ * ‖![w 1, w 2]‖) := by positivity
  unfold stableSecondInputWeight
  dsimp only [H] at Htri ⊢
  nlinarith only [Htri, H0, H1, H2, hcross]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableStrongHessianBudget_input_bound {y : StableState}
    (hb : |y 1| + |y 2| ≤ 1) (v w : StableState) :
    stableStrongHessianBudget y v w ≤ 2 * stableSecondInputWeight (|y 1| + |y 2|) v w := by
  have hv0 : |v 0| ≤ ‖v‖ := norm_le_pi_norm v 0
  have hw0 : |w 0| ≤ ‖w‖ := norm_le_pi_norm w 0
  have hv1 : |v 1| ≤ ‖![v 1, v 2]‖ := norm_le_pi_norm ![v 1, v 2] 0
  have hw1 : |w 1| ≤ ‖![w 1, w 2]‖ := norm_le_pi_norm ![w 1, w 2] 0
  have H0 := mul_le_mul_of_nonneg_right (show |y 1| ≤ |y 1| + |y 2| from le_add_of_nonneg_right (abs_nonneg _))
    (show 0 ≤ ‖v‖ * ‖w‖ by positivity)
  have H1 := mul_le_mul hv0 hw1 (abs_nonneg _) (norm_nonneg _)
  have H2 := mul_le_mul hv1 hw0 (abs_nonneg _) (norm_nonneg _)
  have H3 := mul_le_mul hb (add_le_add (mul_le_mul_of_nonneg_right hv1 (norm_nonneg w))
    (mul_le_mul_of_nonneg_left hw1 (norm_nonneg v))) (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
  unfold stableStrongHessianBudget stableSecondInputWeight
  nlinarith only [H0, H1, H2, H3,
    show 0 ≤ (|y 1| + |y 2|) * ‖v‖ * ‖w‖ by positivity]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableSmallAmplitude_exp_bound {y : StableState}
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) :
    Real.exp (512 * (|y 1| + |y 2|)) ≤ Real.exp 6 :=
  Real.exp_le_exp.mpr (by linarith)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableRescaledFlow_residual_weights {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) :
    |stableRescaledFlow (c + 1) y s 1| + |stableRescaledFlow (c + 1) y s 2| ≤ |y 1| + |y 2| ∧
      |stableRescaledFlow (c + 1) y s 1| ≤ |y 1| * Real.exp (-(c + 1) / 16 * s) := by
  constructor
  · exact (stableRescaledFlow_amplitude_decay hc hm hu hw hs).trans
      ((mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (by linarith))
        (by positivity : 0 ≤ |y 1| + |y 2|)).trans_eq (mul_one _))
  · exact (stableRescaledFlow_wall_decay hc hm hu hw hs).1.trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (abs_nonneg _))

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableRescaledDifferential_residual_weights {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) (v : StableState) :
    let b := |y 1| + |y 2|
    let E := Real.exp 6
    let J := stableRescaledDifferential (c + 1) y s v
    ‖J‖ ≤ E * ‖v‖ ∧ ‖![J 1, J 2]‖ ≤ 256 * E * stableFirstInputWeight b v ∧
      |J 1| ≤ 200 * E * stableFirstInputWeight b v * Real.exp (-(c + 1) / 16 * s) := by
  dsimp only
  let b := |y 1| + |y 2|
  let E := Real.exp 6
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hE : 1 ≤ E := Real.one_le_exp_iff.mpr (by norm_num)
  have hE0 : 0 ≤ E := le_trans (by norm_num) hE
  have hA := stableFirstInputWeight_nonneg hb v
  have hEa := stableSmallAmplitude_exp_bound hu hw
  have hnorm := (stableRescaledDifferential_bound hc hm hu hw hs v).trans
    (mul_le_mul_of_nonneg_right hEa (norm_nonneg v))
  refine ⟨hnorm, ?_, ?_⟩
  · have H := (stableRescaledDifferential_stable_decay hc hm hu hw hs v).trans
      ((mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (by linarith)) (by positivity)).trans_eq (mul_one _))
    have T0 := mul_le_mul_of_nonneg_left hEa (show 0 ≤ 256 * b * ‖v‖ by positivity)
    have T1 := mul_le_mul_of_nonneg_right hE (norm_nonneg (![v 1, v 2] : Fin 2 → ℝ))
    have T2 : 0 ≤ E * ‖![v 1, v 2]‖ := by positivity
    change _ ≤ 256 * E * stableFirstInputWeight b v
    dsimp only [b] at T0
    unfold stableFirstInputWeight
    dsimp only [b, E] at T1 T2 ⊢
    nlinarith only [H, T0, T1, T2]
  · have hv1 : |v 1| ≤ ‖![v 1, v 2]‖ := norm_le_pi_norm ![v 1, v 2] 0
    have hU : |y 1| ≤ b := le_add_of_nonneg_right (abs_nonneg _)
    have T0 := mul_le_mul_of_nonneg_right
      (mul_le_mul hU hEa (Real.exp_pos _).le hb) (norm_nonneg v)
    have T1 := mul_le_mul_of_nonneg_right hE (norm_nonneg (![v 1, v 2] : Fin 2 → ℝ))
    have T2 : 0 ≤ E * ‖![v 1, v 2]‖ := by positivity
    have hcoef : |v 1| + 200 * |y 1| * Real.exp (512 * b) * ‖v‖ ≤
        200 * E * stableFirstInputWeight b v := by
      unfold stableFirstInputWeight
      dsimp only [b, E] at T0 T1 T2 ⊢
      nlinarith only [hv1, T0, T1, T2]
    exact (stableRescaledDifferential_strong_budget hc hm hu hw hs v).trans
      (mul_le_mul hcoef (Real.exp_le_exp.mpr (by nlinarith)) (Real.exp_pos _).le (by positivity))

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableRescaledSecondDifferential_residual_weights {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) (hs : 0 ≤ s) (v w : StableState) :
    let b := |y 1| + |y 2|
    let E := Real.exp 6
    let H := stableRescaledSecondDifferential (c + 1) y s v w
    ‖H‖ ≤ 2400000 * E ^ 3 * stableSecondInputWeight b v w ∧
      |H 1| ≤ 320000000 * E ^ 3 * stableSecondInputWeight b v w * Real.exp (-(c + 1) / 16 * s) := by
  dsimp only
  let b := |y 1| + |y 2|
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hW := stableSecondInputWeight_nonneg hb v w
  have hEa := pow_le_pow_left₀ (Real.exp_pos _).le (stableSmallAmplitude_exp_bound hu.le hw.le) 3
  constructor
  · exact (stableRescaledSecondDifferential_input_bound hc hm hu hw hs v w).trans
      (by nlinarith only [mul_le_mul_of_nonneg_right hEa hW])
  · have hK1 : 1 ≤ c + 1 := by linarith
    have hbudget := stableStrongHessianBudget_input_bound (by linarith : |y 1| + |y 2| ≤ 1) v w
    have hbudget0 := stableStrongHessianBudget_nonneg y v w
    have hprod := mul_le_mul hEa hbudget (stableStrongHessianBudget_nonneg y v w) (by positivity)
    have hdiv := div_le_self (show 0 ≤ 160000000 * Real.exp (512 * b) ^ 3 * stableStrongHessianBudget y v w by positivity) hK1
    have hcoef : 160000000 * Real.exp (512 * b) ^ 3 * stableStrongHessianBudget y v w / (c + 1) ≤
        320000000 * Real.exp 6 ^ 3 * stableSecondInputWeight b v w := by
      dsimp only [b] at hdiv ⊢
      nlinarith only [hdiv, hprod]
    exact (stableRescaledSecondDifferential_strong_decay hc hm hu hw hs v w).trans
      (mul_le_mul hcoef (Real.exp_le_exp.mpr (by nlinarith)) (Real.exp_pos _).le (by positivity))

end
end

theorem solution :
    ∃ C > (0 : ℝ), ∀ (c s : ℝ) (y : StableState), 2 ≤ c → |y 0 - c| < 1 / 40 →
      |y 1| < 1 / 200 → |y 2| < 1 / 200 → 0 ≤ s →
      let b := |y 1| + |y 2|
      let q := Real.exp (-(c + 1) / 16 * s)
      ContDiffAt ℝ 2 (stableRescaledResidualRate (c + 1) s) y ∧
        |stableRescaledResidualRate (c + 1) s y| ≤ C / (c + 1) ^ 2 * |y 1| * b ^ 3 * q ∧
        (∀ v, |fderiv ℝ (stableRescaledResidualRate (c + 1) s) y v| ≤
          C / (c + 1) ^ 2 * b ^ 3 * stableFirstInputWeight b v * q) ∧
        (∀ v w, |fderiv ℝ (fderiv ℝ (stableRescaledResidualRate (c + 1) s)) y v w| ≤
          C / (c + 1) ^ 2 * b ^ 2 * stableFirstInputWeight b v * stableFirstInputWeight b w * q) := by
  obtain ⟨C, hC, HC⟩ := exists_stableRescaledResidualRate_bounds
  let E := Real.exp 6
  let F := 400000000 * E ^ 3
  have hE : 1 ≤ E := Real.one_le_exp_iff.mpr (by norm_num)
  have hE0 : 0 ≤ E := le_trans (by norm_num) hE
  have hF : 0 < F := by dsimp [F, E]; positivity
  have hF1 : 1 ≤ F := by
    have H := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hE 3
    dsimp [F]
    norm_num only [one_pow] at H
    linarith
  have hF969 : 969 * E ≤ F := by
    have H := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hE 2) hE0
    norm_num only [one_pow, mul_one] at H
    dsimp [F]
    nlinarith only [H, hE0]
  refine ⟨F * C, mul_pos hF hC, ?_⟩
  intro c s y hc hm hu hw hs
  dsimp only
  let b := |y 1| + |y 2|
  let q := Real.exp (-(c + 1) / 16 * s)
  let Q := C / (c + 1) ^ 2
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hb1 : b ≤ 1 := by dsimp [b]; linarith
  have hq : 0 ≤ q := (Real.exp_pos _).le
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hscale : F * C / (c + 1) ^ 2 = F * Q := by dsimp [Q]; ring
  rw [hscale]
  obtain ⟨hreg, h0, h1, h2⟩ := HC c s y hc hm hu hw hs
  have hY := stableRescaledFlow_residual_weights hc hm.le hu.le hw.le hs
  have hU : |stableRescaledFlow (c + 1) y s 1| ≤ b * q :=
    hY.2.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (abs_nonneg (y 2))) hq)
  have hJ (v : StableState) := stableRescaledDifferential_residual_weights hc hm.le hu.le hw.le hs v
  have hH (v w : StableState) := stableRescaledSecondDifferential_residual_weights hc hm hu hw hs v w
  refine ⟨hreg, ?_, ?_, ?_⟩
  · have h3 := pow_le_pow_left₀
      (by positivity : 0 ≤ |stableRescaledFlow (c + 1) y s 1| + |stableRescaledFlow (c + 1) y s 2|) hY.1 3
    have H0 := mul_le_mul_of_nonneg_left
      (mul_le_mul hY.2 h3 (by positivity) (by positivity)) hQ
    have H1 := mul_le_mul_of_nonneg_right hF1 (show 0 ≤ Q * |y 1| * b ^ 3 * q by positivity)
    dsimp only [Q, b, q] at H0 H1 ⊢
    nlinarith only [h0, H0, H1]
  · intro v
    have H := stableResidualFirstDecay_bound hb hE0 hq hY.1 hU (hJ v).1 (hJ v).2.1 (hJ v).2.2
    have H0 := mul_le_mul_of_nonneg_left H hQ
    have H1 := mul_le_mul_of_nonneg_right hF969
      (show 0 ≤ Q * b ^ 3 * stableFirstInputWeight b v * q by
        have := stableFirstInputWeight_nonneg hb v
        positivity)
    have R := h1 v
    dsimp only [Q, b, q, E] at H0 H1 ⊢
    nlinarith only [R, H0, H1]
  · intro v w
    have H := stableResidualSecondDecay_bound hb hb1 hE hq hY.1 hU
      (hJ v).1 (hJ w).1 (hJ v).2.1 (hJ w).2.1 (hJ v).2.2 (hJ w).2.2 (hH v w).1 (hH v w).2
    have H0 := mul_le_mul_of_nonneg_left H hQ
    have R := h2 v w
    dsimp only [Q, b, q, E, F] at H0 ⊢
    nlinarith only [R, H0]
