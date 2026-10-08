-- Prove2me | solution 1 for ContinuousMapCalculus.contDiff_postcomp
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-07T09:21:40.597837+00:00
-- url     : https://prove2.me/submissions/519fe4ff-3bfc-470f-a580-c6e3e336ae04

import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Theorems.Thm_ContinuousMapCalculus_hasFDerivAt_of_pointwise
open Set Filter
open scoped Topology ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace ContinuousMapCalculus

universe u v w
variable {K : Type v} {E : Type u} {F : Type w} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A continuous field of linear operators acts pointwise on continuous maps. -/
noncomputable def pointwiseOperator (A : C(K,E →L[ℝ] F)) : C(K,E) →L[ℝ] C(K,F) :=
  LinearMap.mkContinuous
    { toFun := fun v => ⟨fun k => A k (v k), A.continuous.clm_apply v.continuous⟩
      map_add' := fun v w => by ext k; simp
      map_smul' := fun c v => by ext k; simp }
    ‖A‖ (by
      intro v
      change ‖(⟨fun k => A k (v k), A.continuous.clm_apply v.continuous⟩ : C(K,F))‖ ≤ ‖A‖ * ‖v‖
      apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg v))).mpr
      intro k
      exact (A k).le_opNorm (v k) |>.trans
        (mul_le_mul (A.norm_coe_le_norm k) (v.norm_coe_le_norm k)
          (norm_nonneg _) (norm_nonneg _)))

@[simp] theorem pointwiseOperator_apply (A : C(K,E →L[ℝ] F)) (v : C(K,E)) (k : K) :
    pointwiseOperator A v k = A k (v k) := rfl

theorem norm_pointwiseOperator_le (A : C(K,E →L[ℝ] F)) :
    ‖pointwiseOperator A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro v
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg v))).mpr
  intro k
  exact (A k).le_opNorm (v k) |>.trans
    (mul_le_mul (A.norm_coe_le_norm k) (v.norm_coe_le_norm k)
      (norm_nonneg _) (norm_nonneg _))

/-- Lifting an operator field is itself a bounded linear operation. -/
noncomputable def pointwiseOperatorCLM :
    C(K,E →L[ℝ] F) →L[ℝ] (C(K,E) →L[ℝ] C(K,F)) :=
  LinearMap.mkContinuous
    { toFun := fun (A : C(K,E →L[ℝ] F)) => pointwiseOperator A
      map_add' := fun A B => by ext v k; simp
      map_smul' := fun c A => by ext v k; simp }
    1 (by intro A; simpa using norm_pointwiseOperator_le A)


end ContinuousMapCalculus

namespace ContinuousMapCalculus

universe u v
variable {K : Type v} {E F : Type u} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Smooth nonlinear postcomposition on continuous maps from a compact space. -/
theorem contDiff_postcomp_nat (n : ℕ) (f : E → F) (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (fun v : C(K,E) => (⟨f, hf.continuous⟩ : C(E,F)).comp v) := by
  induction n generalizing F with
  | zero =>
    exact contDiff_zero.mpr (ContinuousMap.continuous_postcomp ⟨f, hf.continuous⟩)
  | succ n ih =>
    let d : C(K,E) → C(K,E →L[ℝ] F) :=
      fun v => (⟨fderiv ℝ f, hf.continuous_fderiv (by simp)⟩ : C(E,E →L[ℝ] F)).comp v
    have hd : ContDiff ℝ n d :=
      ih (fderiv ℝ f) (hf.fderiv_right (m := (n : ℕ∞ω)) (by simp))
    let D : C(K,E) → C(K,E) →L[ℝ] C(K,F) :=
      fun v => pointwiseOperator (d v)
    have hL : ContDiff ℝ (n : ℕ∞ω)
        (pointwiseOperatorCLM (K := K) (E := E) (F := F)) :=
      ContinuousLinearMap.contDiff _
    have hD : ContDiff ℝ n D := hL.comp hd
    apply contDiff_succ_iff_hasFDerivAt.mpr
    refine ⟨D, hD, ?_⟩
    intro v
    apply hasFDerivAt_of_pointwise _ D v (hD.continuous.continuousAt)
    intro w k
    have h := (hf.differentiable (by simp) (w k)).hasFDerivAt.comp w
      (ContinuousMap.evalCLM ℝ k).hasFDerivAt
    have he : (ContinuousMap.evalCLM ℝ k).comp (D w) =
        (fderiv ℝ f (w k)).comp (ContinuousMap.evalCLM ℝ k) := by
      ext z
      rfl
    rw [he]
    simpa only [Function.comp_def, ContinuousMap.comp_apply,
      ContinuousMap.coe_mk, ContinuousMap.evalCLM_apply] using h

theorem contDiff_postcomposition_all_orders (f : E → F) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun v : C(K,E) => (⟨f, hf.continuous⟩ : C(E,F)).comp v) := by
  apply contDiff_infty.mpr
  intro n
  exact contDiff_postcomp_nat n f (hf.of_le (mod_cast le_top))

end ContinuousMapCalculus
universe solution_u solution_v
theorem solution {K : Type solution_v} {E F : Type solution_u} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun γ : C(K,E) => (⟨f,hf.continuous⟩ : C(E,F)).comp γ) := by
  exact ContinuousMapCalculus.contDiff_postcomposition_all_orders f hf
