-- Prove2me | solution 1 for FlowCalculus.contDiff_complete_solution_family
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-07T09:25:14.312805+00:00
-- url     : https://prove2.me/submissions/a9b3cd05-4934-41b4-ae8e-667468fe6e26

import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Topology.Order.ProjIcc
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Comp
import Theorems.Thm_ImplicitCalculus_contDiffAt_continuous_solution
import Theorems.Thm_ContinuousMapCalculus_hasFDerivAt_of_pointwise
import Theorems.Thm_ContinuousMapCalculus_contDiff_postcomp
import Theorems.Thm_ContinuousMapCalculus_volterra_residual_isInvertible

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

variable {K E F : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Pairing two continuous maps is a bounded linear operation. -/
noncomputable def pairCLM :
    (C(K,E) × C(K,F)) →L[ℝ] C(K,E × F) :=
  LinearMap.mkContinuous
    { toFun := fun (p : C(K,E) × C(K,F)) =>
        ⟨fun k => (p.1 k,p.2 k), p.1.continuous.prodMk p.2.continuous⟩
      map_add' := fun p q => by ext k <;> rfl
      map_smul' := fun c p => by ext k <;> rfl }
    1 (by
      intro p
      change ‖(⟨fun k => (p.1 k,p.2 k), _⟩ : C(K,E × F))‖ ≤ 1 * ‖p‖
      rw [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg p)).mpr
      intro k
      rw [Prod.norm_def, Prod.norm_def]
      exact max_le_max (p.1.norm_coe_le_norm k) (p.2.norm_coe_le_norm k))

end ContinuousMapCalculus


open Set MeasureTheory
open scoped Topology ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace ContinuousMapCalculus

abbrev UnitInterval := Icc (0 : ℝ) 1

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

noncomputable def extendUnitInterval (f : C(UnitInterval,V)) : C(ℝ,V) :=
  f.comp ⟨projIcc 0 1 zero_le_one, continuous_projIcc⟩

@[simp] theorem extendUnitInterval_apply (f : C(UnitInterval,V)) (t : UnitInterval) :
    extendUnitInterval f t = f t := by
  simp [extendUnitInterval, projIcc, t.property.1, t.property.2]

/-- Variable-upper-endpoint integration, as a curve on the unit interval. -/
noncomputable def primitive (f : C(UnitInterval,V)) : C(UnitInterval,V) :=
  ⟨fun t => ∫ s in 0..(t:ℝ), extendUnitInterval f s,
    ((intervalIntegral.differentiable_integral_of_continuous
      (extendUnitInterval f).continuous).continuous.comp continuous_subtype_val)⟩

theorem norm_primitive_le (f : C(UnitInterval,V)) : ‖primitive f‖ ≤ ‖f‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
  intro t
  change ‖∫ s in 0..(t:ℝ), extendUnitInterval f s‖ ≤ ‖f‖
  calc
    _ ≤ ‖f‖ * |(t:ℝ) - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const
        (fun s _ => f.norm_coe_le_norm _)
    _ ≤ ‖f‖ := by
      rw [sub_zero, abs_of_nonneg t.property.1]
      exact mul_le_of_le_one_right (norm_nonneg _) t.property.2

/-- Integration from zero has operator norm at most one in the supremum norm. -/
noncomputable def primitiveCLM : C(UnitInterval,V) →L[ℝ] C(UnitInterval,V) :=
  LinearMap.mkContinuous
    { toFun := fun (f : C(UnitInterval,V)) => primitive f
      map_add' := fun f g => by
        ext t
        exact intervalIntegral.integral_add
          ((extendUnitInterval f).continuous.intervalIntegrable 0 t)
          ((extendUnitInterval g).continuous.intervalIntegrable 0 t)
      map_smul' := fun c f => by
        ext t
        exact intervalIntegral.integral_smul c _ }
    1 (by intro f; simpa using norm_primitive_le f)

theorem norm_primitiveCLM_le : ‖(primitiveCLM : C(UnitInterval,V) →L[ℝ] C(UnitInterval,V))‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖primitive f‖ ≤ 1 * ‖f‖
  simpa using norm_primitive_le f

end ContinuousMapCalculus

namespace ContinuousMapCalculus

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

def timeIdentity : C(UnitInterval,ℝ) := ⟨Subtype.val, continuous_subtype_val⟩

noncomputable def fieldCurve (X : ℝ → V → V)
    (hX : Continuous (fun p : ℝ × V => X p.1 p.2))
    (t : ℝ) (γ : C(UnitInterval,V)) : C(UnitInterval,V) :=
  ⟨fun s => X (t*s) (γ s), hX.comp
    ((continuous_const.mul continuous_subtype_val).prodMk γ.continuous)⟩

theorem contDiff_fieldCurve (X : ℝ → V → V)
    (hX : ContDiff ℝ ∞ (fun p : ℝ × V => X p.1 p.2)) :
    ContDiff ℝ ∞ (fun p : ℝ × C(UnitInterval,V) => fieldCurve X hX.continuous p.1 p.2) := by
  have hpair : ContDiff ℝ ∞ (fun p : ℝ × C(UnitInterval,V) =>
      pairCLM (p.1 • timeIdentity, p.2)) := by
    have ht : ContDiff ℝ ∞ (fun p : ℝ × C(UnitInterval,V) => p.1 • timeIdentity) :=
      contDiff_fst.smul (contDiff_const (c := timeIdentity))
    exact (pairCLM (K := UnitInterval) (E := ℝ) (F := V)).contDiff.comp
      (ht.prodMk contDiff_snd)
  have hs := (contDiff_postcomp (K := UnitInterval)
    (fun p : ℝ × V => X p.1 p.2) hX).comp hpair
  exact hs

noncomputable def rescaledCurve (ψ : ℝ → V → V)
    (hc : Continuous (fun p : ℝ × V => ψ p.1 p.2)) (p : ℝ × V) : C(UnitInterval,V) :=
  ⟨fun s => ψ (p.1*s) p.2, hc.comp
    ((continuous_const.mul continuous_subtype_val).prodMk continuous_const)⟩

theorem continuous_rescaledCurve (ψ : ℝ → V → V)
    (hc : Continuous (fun p : ℝ × V => ψ p.1 p.2)) :
    Continuous (rescaledCurve ψ hc) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact hc.comp ((continuous_fst.fst.mul continuous_snd.subtype_val).prodMk continuous_fst.snd)

theorem rescaledCurve_integral_eq (X ψ : ℝ → V → V)
    (hX : Continuous (fun p : ℝ × V => X p.1 p.2))
    (hc : Continuous (fun p : ℝ × V => ψ p.1 p.2))
    (h0 : ∀ y, ψ 0 y = y)
    (hd : ∀ t y, HasDerivAt (fun s => ψ s y) (X t (ψ t y)) t)
    (p : ℝ × V) :
    rescaledCurve ψ hc p = ContinuousMap.const UnitInterval p.2 +
      p.1 • primitiveCLM (fieldCurve X hX p.1 (rescaledCurve ψ hc p)) := by
  ext s
  have hder : ∀ r : ℝ, HasDerivAt (fun r => ψ (p.1*r) p.2)
      (p.1 • X (p.1*r) (ψ (p.1*r) p.2)) r := by
    intro r
    simpa only [Function.comp_def, mul_one] using
      (hd (p.1*r) p.2).scomp r ((hasDerivAt_id r).const_mul p.1)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _ => hder r)
    ((hX.comp ((continuous_const.mul continuous_id).prodMk
      (hc.comp ((continuous_const.mul continuous_id).prodMk continuous_const)))).const_smul p.1
        |>.intervalIntegrable 0 (s:ℝ))
  have he : (∫ r in 0..(s:ℝ), extendUnitInterval
      (fieldCurve X hX p.1 (rescaledCurve ψ hc p)) r) =
      ∫ r in 0..(s:ℝ), X (p.1*r) (ψ (p.1*r) p.2) := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hrI : r ∈ Icc (0:ℝ) 1 := by
      rw [uIcc_of_le s.property.1] at hr
      exact ⟨hr.1, hr.2.trans s.property.2⟩
    exact extendUnitInterval_apply _ ⟨r,hrI⟩
  change ψ (p.1*s) p.2 = p.2 + p.1 • ∫ r in 0..(s:ℝ), _
  rw [he]
  rw [intervalIntegral.integral_smul] at hi
  simp only [mul_zero, h0] at hi
  exact (eq_add_of_sub_eq hi.symm).trans (add_comm _ _)

end ContinuousMapCalculus

namespace ContinuousMapCalculus

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

theorem contDiff_spatialDerivative (X : ℝ → V → V)
    (hX : ContDiff ℝ ∞ (fun p : ℝ × V => X p.1 p.2)) :
    ContDiff ℝ ∞ (fun p : ℝ × V => fderiv ℝ (X p.1) p.2) := by
  have hh : ContDiff ℝ ∞ (fun p : (ℝ × V) × V => X p.1.1 p.2) :=
    hX.comp (contDiff_fst.fst.prodMk contDiff_snd)
  exact hh.fderiv contDiff_snd (by simp)

noncomputable def spatialDerivativeCurve (X : ℝ → V → V)
    (hX : ContDiff ℝ ∞ (fun p : ℝ × V => X p.1 p.2))
    (t : ℝ) (γ : C(UnitInterval,V)) : C(UnitInterval,V →L[ℝ] V) :=
  ⟨fun s => fderiv ℝ (X (t*s)) (γ s), (contDiff_spatialDerivative X hX).continuous.comp
    ((continuous_const.mul continuous_subtype_val).prodMk γ.continuous)⟩

theorem hasFDerivAt_fieldCurve (X : ℝ → V → V)
    (hX : ContDiff ℝ ∞ (fun p : ℝ × V => X p.1 p.2))
    (t : ℝ) (γ : C(UnitInterval,V)) :
    HasFDerivAt (fieldCurve X hX.continuous t)
      (pointwiseOperator (spatialDerivativeCurve X hX t γ)) γ := by
  have hdc : Continuous (fun γ : C(UnitInterval,V) => spatialDerivativeCurve X hX t γ) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact (contDiff_spatialDerivative X hX).continuous.comp
      ((continuous_const.mul continuous_snd.subtype_val).prodMk continuous_eval)
  apply hasFDerivAt_of_pointwise _ (fun γ => pointwiseOperator (spatialDerivativeCurve X hX t γ)) γ
    ((pointwiseOperatorCLM (K := UnitInterval) (E := V) (F := V)).continuous.comp hdc).continuousAt
  intro η s
  have ht : ContDiff ℝ ∞ (X (t*s)) := hX.comp (contDiff_const.prodMk contDiff_id)
  have h := (ht.differentiable (by simp) (η s)).hasFDerivAt.comp η
    (ContinuousMap.evalCLM ℝ s).hasFDerivAt
  have he : (ContinuousMap.evalCLM ℝ s).comp
      (pointwiseOperator (spatialDerivativeCurve X hX t η)) =
      (fderiv ℝ (X (t*s)) (η s)).comp (ContinuousMap.evalCLM ℝ s) := by ext v; rfl
  rw [he]
  simpa only [fieldCurve, ContinuousMap.coe_mk, Function.comp_def,
    ContinuousMap.evalCLM_apply] using h

end ContinuousMapCalculus

open ContinuousMapCalculus

theorem solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (X ψ : ℝ → V → V)
    (hX : ContDiff ℝ ∞ (fun p : ℝ × V => X p.1 p.2))
    (hc : Continuous (fun p : ℝ × V => ψ p.1 p.2))
    (h0 : ∀ y, ψ 0 y = y)
    (hd : ∀ t y, HasDerivAt (fun s => ψ s y) (X t (ψ t y)) t) :
    ContDiff ℝ ∞ (fun p : ℝ × V => ψ p.1 p.2) := by
  let r := rescaledCurve ψ hc
  let Φ : (ℝ × V) × C(UnitInterval,V) → C(UnitInterval,V) := fun q =>
    (ContinuousLinearMap.const ℝ UnitInterval) q.1.2 +
      q.1.1 • primitiveCLM (fieldCurve X hX.continuous q.1.1 q.2)
  let G : (ℝ × V) × C(UnitInterval,V) → C(UnitInterval,V) := fun q => q.2 - Φ q
  have hfield : ContDiff ℝ ∞ (fun q : (ℝ × V) × C(UnitInterval,V) =>
      fieldCurve X hX.continuous q.1.1 q.2) :=
    (contDiff_fieldCurve X hX).comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hΦ : ContDiff ℝ ∞ Φ := by
    have hi : ContDiff ℝ ∞ (fun q : (ℝ × V) × C(UnitInterval,V) =>
        primitiveCLM (fieldCurve X hX.continuous q.1.1 q.2)) :=
      (primitiveCLM (V := V)).contDiff.comp hfield
    have hconst : ContDiff ℝ ∞ (fun q : (ℝ × V) × C(UnitInterval,V) =>
        (ContinuousLinearMap.const ℝ UnitInterval) q.1.2) :=
      (ContinuousLinearMap.const ℝ UnitInterval (M := V)).contDiff.comp contDiff_fst.snd
    exact hconst.add (contDiff_fst.fst.smul hi)
  have hG : ContDiff ℝ ∞ G := contDiff_snd.sub hΦ
  have heq : ∀ p, Φ (p,r p) = r p := fun p =>
    (rescaledCurve_integral_eq X ψ hX.continuous hc h0 hd p).symm
  have hr : ContDiff ℝ ∞ r := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    let A := spatialDerivativeCurve X hX p.1 (r p)
    let L : C(UnitInterval,V) →L[ℝ] C(UnitInterval,V) :=
      p.1 • primitiveCLM.comp (pointwiseOperator A)
    have hp : HasFDerivAt (fun γ => Φ (p,γ)) L (r p) := by
      have h := ((primitiveCLM (V := V)).hasFDerivAt.comp (r p)
        (hasFDerivAt_fieldCurve X hX p.1 (r p))).const_smul p.1
      exact h.const_add ((ContinuousLinearMap.const ℝ UnitInterval) p.2)
    have hg : HasFDerivAt (fun γ => G (p,γ))
        (ContinuousLinearMap.id ℝ C(UnitInterval,V) - L) (r p) :=
      (hasFDerivAt_id (r p)).sub hp
    have hlinear : L = primitiveCLM.comp (pointwiseOperator (p.1 • A)) := by
      ext γ s
      change p.1 • (∫ u in 0..(s:ℝ), extendUnitInterval (pointwiseOperator A γ) u) =
        ∫ u in 0..(s:ℝ), extendUnitInterval (pointwiseOperator (p.1 • A) γ) u
      rw [← intervalIntegral.integral_smul]
      rfl
    have hD : (fderiv ℝ G (p,r p)).comp (ContinuousLinearMap.inr ℝ (ℝ × V) C(UnitInterval,V)) =
        ContinuousLinearMap.id ℝ C(UnitInterval,V) - L := by
      have h := (hG.differentiable (by simp) (p,r p)).hasFDerivAt.comp (r p)
        (hasFDerivAt_prodMk_right p (r p))
      exact h.unique hg
    apply ImplicitCalculus.contDiffAt_continuous_solution ∞ (by simp) G r p
      hG.contDiffAt (continuous_rescaledCurve ψ hc).continuousAt
    · rw [hD, hlinear]
      exact ContinuousMapCalculus.volterra_residual_isInvertible (p.1 • A)
        (primitiveCLM.comp (pointwiseOperator (p.1 • A))) (by intro γ s; rfl)
    · apply Filter.Eventually.of_forall
      intro q
      simp only [G, heq, sub_self]
  have hev : ContDiff ℝ ∞
      (ContinuousMap.evalCLM ℝ (M := V) (⟨1,zero_le_one,le_rfl⟩ : UnitInterval)) :=
    ContinuousLinearMap.contDiff _
  have hend : ContDiff ℝ ∞ (fun p => (r p) (⟨1,zero_le_one,le_rfl⟩ : UnitInterval)) :=
    hev.comp hr
  simpa only [r, rescaledCurve, ContinuousMap.coe_mk, mul_one] using hend
