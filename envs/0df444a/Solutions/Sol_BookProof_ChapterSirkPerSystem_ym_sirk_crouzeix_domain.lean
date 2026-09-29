-- Prove2me | solution 1 for BookProof.ChapterSirkPerSystem.ym_sirk_crouzeix_domain
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T10:12:48.313067+00:00
-- url     : https://prove2.me/submissions/9c2b6aef-687f-4219-a236-af4c1f48e517

/- Adapted from Leonardo Pedro, timepiece commit 61595bc, Apache-2.0.
https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsHermite.lean
https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFriedrichsExtension.lean -/
import Definitions.Def_ChapterSirkPerSystem
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterComplexShiftCore
import Mathlib
set_option maxHeartbeats 4000000
noncomputable section
namespace SirkFriedrichsAux
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert BookProof.FriedrichsExtension BookProof.FriedrichsExtension.FormDom
open Filter Topology
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] {Dom : Submodule ℂ F}
@[simp] private theorem shiftMap_apply (A : Dom →ₗ[ℂ] F) (γ : ℝ) (x : Dom) :
    shiftMap A γ x = A x + (γ : ℂ) • (x : F) := rfl

private theorem preim_eq (R : F →L[ℂ] F) (hinj : Function.Injective R)
    (y : LinearMap.range (R : F →ₗ[ℂ] F)) {u : F} (hu : R u = (y : F)) : preim R y = u :=
  hinj (by rw [preim_spec, hu])

@[simp] private theorem invShiftOperator_apply (R : F →L[ℂ] F) (hinj : Function.Injective R) (γ : ℝ)
    (y : LinearMap.range (R : F →ₗ[ℂ] F)) :
    invShiftOperator R hinj γ y = preim R y - (γ : ℂ) • (y : F) := rfl

private theorem isShiftInvert_invShiftOperator (R : F →L[ℂ] F) (hinj : Function.Injective R) (γ : ℝ) :
    IsShiftInvert (invShiftOperator R hinj γ) γ R := by
  constructor
  · intro x
    have hx : shiftMap (invShiftOperator R hinj γ) γ x = preim R x := by
      simp [shiftMap_apply]
    rw [hx, preim_spec]
  · intro u
    refine ⟨⟨u, rfl⟩, ?_⟩
    have hpre : preim R ⟨R u, ⟨u, rfl⟩⟩ = u := preim_eq R hinj _ rfl
    simp [shiftMap_apply, hpre]

private theorem invShiftOperator_symmetricOn (R : F →L[ℂ] F) (hinj : Function.Injective R) (γ : ℝ)
    (hR : IsSelfAdjoint R) :
    SymmetricOn (LinearMap.range (R : F →ₗ[ℂ] F)) (invShiftOperator R hinj γ) := by
  have hRsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hR
  intro y z
  have hy : R (preim R y) = (y : F) := preim_spec R y
  have hz : R (preim R z) = (z : F) := preim_spec R z
  have hcross : (inner ℂ (preim R y) (z : F) : ℂ) = inner ℂ (y : F) (preim R z) := by
    rw [← hy, ← hz]
    exact (hRsym (preim R y) (preim R z)).symm
  simp only [invShiftOperator_apply, inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right, Complex.conj_ofReal, hcross]

private theorem invShiftOperator_quadForm_nonneg (R : F →L[ℂ] F) (hinj : Function.Injective R) (γ : ℝ)
    (hposR : ∀ u : F, γ * ‖R u‖ ^ 2 ≤ (inner ℂ (R u) u : ℂ).re)
    (y : LinearMap.range (R : F →ₗ[ℂ] F)) : 0 ≤ quadForm (invShiftOperator R hinj γ) y := by
  have hy : R (preim R y) = (y : F) := preim_spec R y
  have hq : quadForm (invShiftOperator R hinj γ) y
      = (inner ℂ (y : F) (preim R y) : ℂ).re - γ * ‖(y : F)‖ ^ 2 := by
    rw [quadForm, invShiftOperator_apply, inner_sub_right, inner_smul_right, Complex.sub_re,
      inner_self_eq_norm_sq_to_K]
    congr 1
    simp [← Complex.ofReal_pow]
  have hp := hposR (preim R y)
  rw [hy] at hp
  rw [hq]
  linarith

private theorem invShiftOperator_selfAdjointCriterion (R : F →L[ℂ] F) (hinj : Function.Injective R)
    (γ : ℝ) (hR : IsSelfAdjoint R) (w u : F)
    (hw : ∀ v : LinearMap.range (R : F →ₗ[ℂ] F),
      (inner ℂ (invShiftOperator R hinj γ v) w : ℂ) = inner ℂ (v : F) u) :
    ∃ h : w ∈ LinearMap.range (R : F →ₗ[ℂ] F), invShiftOperator R hinj γ ⟨w, h⟩ = u := by
  have hRsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hR
  have hkey : ∀ z : F, (inner ℂ z (w - (γ : ℂ) • R w - R u) : ℂ) = 0 := by
    intro z
    have hv := hw ⟨R z, ⟨z, rfl⟩⟩
    have hpre : preim R ⟨R z, ⟨z, rfl⟩⟩ = z := preim_eq R hinj _ rfl
    rw [invShiftOperator_apply, hpre] at hv
    have h1 : (inner ℂ (R z) w : ℂ) = inner ℂ z (R w) := hRsym z w
    have h2 : (inner ℂ (R z) u : ℂ) = inner ℂ z (R u) := hRsym z u
    rw [inner_sub_left, inner_smul_left, Complex.conj_ofReal, h1, h2] at hv
    rw [inner_sub_right, inner_sub_right, inner_smul_right]
    rw [hv]
    ring
  have hzero : w - (γ : ℂ) • R w - R u = 0 :=
    inner_self_eq_zero.mp (hkey (w - (γ : ℂ) • R w - R u))
  have hwsum : w = (γ : ℂ) • R w + R u := by
    linear_combination (norm := module) hzero
  have hwval : w = R (u + (γ : ℂ) • w) := by
    rw [map_add, map_smul]
    linear_combination (norm := module) hwsum
  refine ⟨⟨u + (γ : ℂ) • w, hwval.symm⟩, ?_⟩
  have hpre : preim R ⟨w, ⟨u + (γ : ℂ) • w, hwval.symm⟩⟩ = u + (γ : ℂ) • w :=
    preim_eq R hinj _ hwval.symm
  rw [invShiftOperator_apply, hpre]
  module

private theorem invShiftOperator_isPositiveSelfAdjointExtension (R : F →L[ℂ] F)
    (hinj : Function.Injective R) (γ : ℝ) (hR : IsSelfAdjoint R)
    (hposR : ∀ u : F, γ * ‖R u‖ ^ 2 ≤ (inner ℂ (R u) u : ℂ).re)
    {D : Submodule ℂ F} (hD : D ≤ LinearMap.range (R : F →ₗ[ℂ] F)) (H : D →ₗ[ℂ] F)
    (hH : ∀ x : D, H x = invShiftOperator R hinj γ ⟨(x : F), hD x.2⟩) :
    IsPositiveSelfAdjointExtension H (invShiftOperator R hinj γ) :=
  ⟨fun x => ⟨hD x.2, (hH x).symm⟩, invShiftOperator_symmetricOn R hinj γ hR,
    invShiftOperator_quadForm_nonneg R hinj γ hposR,
    invShiftOperator_selfAdjointCriterion R hinj γ hR⟩

@[simp] private theorem incl_apply {P : PosSymOp F} (x : FormDom P) : incl P x = toAmbient x := rfl

private theorem isUniformInducing_toComplL (P : PosSymOp F) :
    IsUniformInducing (UniformSpace.Completion.toComplL (𝕜 := ℂ) (E := FormDom P)) := by
  simpa [UniformSpace.Completion.coe_toComplL] using
    UniformSpace.Completion.isUniformInducing_coe (FormDom P)

@[simp] private theorem formExt_coe (P : PosSymOp F) (x : FormDom P) :
    formExt P (x : FormSpace P) = toAmbient x := by
  have := ContinuousLinearMap.extend_eq (incl P) (denseRange_toComplL P)
    (isUniformInducing_toComplL P) x
  simpa [formExt, UniformSpace.Completion.coe_toComplL] using this

private theorem inner_coe_eq (P : PosSymOp F) (x : FormDom P) (k : FormSpace P) :
    (inner ℂ (x : FormSpace P) k : ℂ)
      = inner ℂ (toAmbient x + P.op (toDom x)) (formExt P k) := by
  refine UniformSpace.Completion.induction_on k ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro y
    rw [formExt_coe, UniformSpace.Completion.inner_coe, inner_def, inner_add_left,
      toAmbient_eq, toAmbient_eq, P.sym (toDom x) (toDom y)]

private theorem formExt_injective (P : PosSymOp F) : Function.Injective (formExt P) := by
  rw [injective_iff_map_eq_zero]
  intro k hk
  have hzero : ∀ y : FormDom P, (inner ℂ (y : FormSpace P) k : ℂ) = 0 := by
    intro y
    rw [inner_coe_eq, hk, inner_zero_right]
  have hall : ∀ z : FormSpace P, (inner ℂ z k : ℂ) = 0 := by
    intro z
    refine UniformSpace.Completion.induction_on z ?_ hzero
    exact isClosed_eq (by fun_prop) (by fun_prop)
  simpa using hall k

private theorem dense_range_formExt (P : PosSymOp F) (hdense : Dense (P.dom : Set F)) :
    Dense (Set.range (formExt P)) := by
  refine Dense.mono ?_ hdense
  intro v hv
  exact ⟨((show FormDom P from ⟨v, hv⟩ : FormDom P) : FormSpace P), by rw [formExt_coe]; rfl⟩

@[simp] private theorem friedrichsResolvent_apply (P : PosSymOp F) (u : F) :
    friedrichsResolvent P u = formExt P (formRiesz P u) := rfl

private theorem inner_friedrichsResolvent (P : PosSymOp F) (u v : F) :
    (inner ℂ u (friedrichsResolvent P v) : ℂ) = inner ℂ (formRiesz P u) (formRiesz P v) := by
  rw [friedrichsResolvent_apply, formRiesz_spec]

private theorem friedrichsResolvent_isSelfAdjoint (P : PosSymOp F) :
    IsSelfAdjoint (friedrichsResolvent P) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro u v
  simp only [ContinuousLinearMap.coe_coe]
  rw [← inner_conj_symm, inner_friedrichsResolvent, inner_friedrichsResolvent, inner_conj_symm]

private theorem friedrichsResolvent_pos (P : PosSymOp F) (u : F) :
    (1 : ℝ) * ‖friedrichsResolvent P u‖ ^ 2
      ≤ (inner ℂ (friedrichsResolvent P u) u : ℂ).re := by
  have h : (inner ℂ (friedrichsResolvent P u) u : ℂ)
      = starRingEnd ℂ (inner ℂ u (friedrichsResolvent P u)) := (inner_conj_symm _ _).symm
  rw [h, inner_friedrichsResolvent]
  have h2 : (inner ℂ (formRiesz P u) (formRiesz P u) : ℂ) = ((‖formRiesz P u‖ ^ 2 : ℝ) : ℂ) := by
    simp [inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
  rw [h2]
  simp only [Complex.conj_ofReal, Complex.ofReal_re, one_mul, friedrichsResolvent_apply]
  nlinarith [norm_formExt_apply_le P (formRiesz P u), norm_nonneg (formExt P (formRiesz P u)),
    norm_nonneg (formRiesz P u)]

private theorem friedrichsResolvent_injective (P : PosSymOp F) (hdense : Dense (P.dom : Set F)) :
    Function.Injective (friedrichsResolvent P) := by
  rw [injective_iff_map_eq_zero]
  intro u hu
  have h0 : formRiesz P u = 0 := formExt_injective P (by simpa using hu)
  have hall : ∀ k : FormSpace P, (inner ℂ u (formExt P k) : ℂ) = 0 := by
    intro k
    rw [← formRiesz_spec, h0, inner_zero_left]
  have hzero : ∀ v : F, (inner ℂ u v : ℂ) = 0 := by
    intro v
    have hc : Continuous fun w : F => (inner ℂ u w : ℂ) := (innerSL ℂ u).continuous
    have heq : Set.EqOn (fun w : F => (inner ℂ u w : ℂ)) (fun _ => (0 : ℂ))
        (Set.range (formExt P)) := by
      rintro _ ⟨k, rfl⟩
      exact hall k
    exact congrFun (Continuous.ext_on (dense_range_formExt P hdense) hc continuous_const heq) v
  simpa using hzero u

private theorem friedrichsResolvent_shift (P : PosSymOp F) (x : P.dom) :
    friedrichsResolvent P ((x : F) + P.op x) = (x : F) := by
  have hx : formRiesz P ((x : F) + P.op x)
      = ((show FormDom P from x : FormDom P) : FormSpace P) := by
    refine ext_inner_right ℂ (fun k => ?_)
    rw [formRiesz_spec, inner_coe_eq]
    rfl
  rw [friedrichsResolvent_apply, hx, formExt_coe]
  rfl

private theorem dom_le_range (P : PosSymOp F) :
    P.dom ≤ LinearMap.range (friedrichsResolvent P : F →ₗ[ℂ] F) := by
  intro v hv
  exact ⟨(v : F) + P.op ⟨v, hv⟩, friedrichsResolvent_shift P ⟨v, hv⟩⟩

private theorem friedrichs_extension_exists (P : PosSymOp F) (hdense : Dense (P.dom : Set F)) :
    ∃ (Dom : Submodule ℂ F) (A : Dom →ₗ[ℂ] F), IsPositiveSelfAdjointExtension P.op A := by
  have hinj : Function.Injective (friedrichsResolvent P) :=
    friedrichsResolvent_injective P hdense
  refine ⟨_, invShiftOperator (friedrichsResolvent P) hinj 1, ?_⟩
  refine invShiftOperator_isPositiveSelfAdjointExtension (friedrichsResolvent P) hinj 1
    (friedrichsResolvent_isSelfAdjoint P) (friedrichsResolvent_pos P) (dom_le_range P) P.op ?_
  intro x
  have hpre : preim (friedrichsResolvent P) ⟨(x : F), dom_le_range P x.2⟩
      = (x : F) + P.op x :=
    preim_eq _ hinj _ (friedrichsResolvent_shift P x)
  rw [invShiftOperator_apply, hpre]
  push_cast
  module

private theorem formSpace_norm_bound (P : PosSymOp F) {mu : ℝ}
    (hmu : ∀ x : P.dom, mu * ‖(x : F)‖ ^ 2 ≤ quadForm P.op x) (k : FormSpace P) :
    (1 + mu) * ‖formExt P k‖ ^ 2 ≤ ‖k‖ ^ 2 := by
  refine UniformSpace.Completion.induction_on k ?_ ?_
  · exact isClosed_le (by fun_prop) (by fun_prop)
  · intro x
    have hnorm : ‖((x : FormSpace P))‖ = ‖x‖ := UniformSpace.Completion.norm_coe x
    have hsq := norm_sq_eq x
    have hq : (inner ℂ (toAmbient x) (P.op (toDom x)) : ℂ).re = quadForm P.op (toDom x) := by
      rw [quadForm, toAmbient_eq]
    have hb := hmu (toDom x)
    have hxa : ((toDom x : P.dom) : F) = toAmbient x := (toAmbient_eq x).symm
    rw [hxa] at hb
    rw [formExt_coe, hnorm, hsq, hq]
    linarith

private theorem friedrichs_quadForm_lower_bound (P : PosSymOp F)
    (hinj : Function.Injective (friedrichsResolvent P)) {mu : ℝ}
    (hmu : ∀ x : P.dom, mu * ‖(x : F)‖ ^ 2 ≤ quadForm P.op x)
    (y : LinearMap.range ((friedrichsResolvent P) : F →ₗ[ℂ] F)) :
    mu * ‖(y : F)‖ ^ 2 ≤ quadForm (invShiftOperator (friedrichsResolvent P) hinj 1) y := by
  have hy : friedrichsResolvent P (preim (friedrichsResolvent P) y) = (y : F) :=
    preim_spec _ y
  -- the quadratic form of `A = S⁻¹ − 1` at `y = S u`
  have hq : quadForm (invShiftOperator (friedrichsResolvent P) hinj 1) y
      = (inner ℂ (y : F) (preim (friedrichsResolvent P) y) : ℂ).re - 1 * ‖(y : F)‖ ^ 2 := by
    rw [quadForm, invShiftOperator_apply, inner_sub_right, inner_smul_right, Complex.sub_re,
      inner_self_eq_norm_sq_to_K]
    congr 1
    simp [← Complex.ofReal_pow]
  -- `⟪y, u⟫ = ⟪S u, u⟫ = ‖formRiesz u‖²`
  have hyu : (inner ℂ (y : F) (preim (friedrichsResolvent P) y) : ℂ).re
      = ‖formRiesz P (preim (friedrichsResolvent P) y)‖ ^ 2 := by
    have h1 : (inner ℂ (y : F) (preim (friedrichsResolvent P) y) : ℂ)
        = starRingEnd ℂ (inner ℂ (preim (friedrichsResolvent P) y)
            (friedrichsResolvent P (preim (friedrichsResolvent P) y)) : ℂ) := by
      rw [← inner_conj_symm, hy]
    rw [h1, inner_friedrichsResolvent, Complex.conj_re]
    exact re_inner_self (F := FormSpace P) _
  -- and `formExt (formRiesz u) = S u = y`
  have hext : formExt P (formRiesz P (preim (friedrichsResolvent P) y)) = (y : F) := by
    rw [← hy, friedrichsResolvent_apply]
  have hbound := formSpace_norm_bound P hmu (formRiesz P (preim (friedrichsResolvent P) y))
  rw [hext] at hbound
  rw [hq, hyu]
  nlinarith [hbound]

private theorem friedrichs_extension_form_gap (P : PosSymOp F) (hdense : Dense (P.dom : Set F))
    {mu : ℝ} (hmu : ∀ x : P.dom, mu * ‖(x : F)‖ ^ 2 ≤ quadForm P.op x) :
    ∃ (Dom : Submodule ℂ F) (A : Dom →ₗ[ℂ] F) (S : F →L[ℂ] F),
      IsPositiveSelfAdjointExtension P.op A ∧ IsShiftInvert A 1 S ∧
        IsSelfAdjoint S ∧ (∀ y : Dom, mu * ‖(y : F)‖ ^ 2 ≤ quadForm A y) := by
  have hinj : Function.Injective (friedrichsResolvent P) :=
    friedrichsResolvent_injective P hdense
  refine ⟨_, invShiftOperator (friedrichsResolvent P) hinj 1, friedrichsResolvent P, ?_,
    isShiftInvert_invShiftOperator _ hinj 1, friedrichsResolvent_isSelfAdjoint P,
    friedrichs_quadForm_lower_bound P hinj hmu⟩
  refine invShiftOperator_isPositiveSelfAdjointExtension (friedrichsResolvent P) hinj 1
    (friedrichsResolvent_isSelfAdjoint P) (friedrichsResolvent_pos P) (dom_le_range P) P.op ?_
  intro x
  have hpre : preim (friedrichsResolvent P) ⟨(x : F), dom_le_range P x.2⟩
      = (x : F) + P.op x :=
    preim_eq _ hinj _ (friedrichsResolvent_shift P x)
  rw [invShiftOperator_apply, hpre]
  push_cast
  module

end SirkFriedrichsAux
namespace BookProof.YangMillsHermite
open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert
variable {d : ℕ}
@[simp] theorem starP_add (p q : MvPolynomial (Fin d) ℂ) :
    starP (p + q) = starP p + starP q := map_add _ _ _

@[simp] theorem starP_mul (p q : MvPolynomial (Fin d) ℂ) :
    starP (p * q) = starP p * starP q := map_mul _ _ _

@[simp] theorem starP_X (j : Fin d) : starP (X j : MvPolynomial (Fin d) ℂ) = X j := by
  simp [starP]

@[simp] theorem starP_C (c : ℂ) : starP (C c : MvPolynomial (Fin d) ℂ) = C ((starRingEnd ℂ) c) := by
  simp [starP]

@[simp] theorem starP_zero : starP (0 : MvPolynomial (Fin d) ℂ) = 0 := map_zero _

theorem starP_sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin d) ℂ) :
    starP (∑ i ∈ s, f i) = ∑ i ∈ s, starP (f i) := map_sum _ _ _

theorem starP_smul (c : ℂ) (p : MvPolynomial (Fin d) ℂ) :
    starP (c • p) = ((starRingEnd ℂ) c) • starP p := by
  rw [smul_eq_C_mul, starP_mul, starP_C, smul_eq_C_mul]

theorem starP_real_smul (t : ℝ) (p : MvPolynomial (Fin d) ℂ) :
    starP ((t : ℂ) • p) = (t : ℂ) • starP p := by
  rw [starP_smul, Complex.conj_ofReal]

theorem RealCoeff.add {p q : MvPolynomial (Fin d) ℂ} (hp : RealCoeff p) (hq : RealCoeff q) :
    RealCoeff (p + q) := by
  change starP (p + q) = p + q
  rw [starP_add, show starP p = p from hp, show starP q = q from hq]

theorem RealCoeff.mul {p q : MvPolynomial (Fin d) ℂ} (hp : RealCoeff p) (hq : RealCoeff q) :
    RealCoeff (p * q) := by
  change starP (p * q) = p * q
  rw [starP_mul, show starP p = p from hp, show starP q = q from hq]

theorem RealCoeff.smul {t : ℝ} {p : MvPolynomial (Fin d) ℂ} (hp : RealCoeff p) :
    RealCoeff ((t : ℂ) • p) := by
  rw [RealCoeff, starP_real_smul, hp]

theorem RealCoeff.sum {ι : Type*} {s : Finset ι} {f : ι → MvPolynomial (Fin d) ℂ}
    (h : ∀ i ∈ s, RealCoeff (f i)) : RealCoeff (∑ i ∈ s, f i) := by
  rw [RealCoeff, starP_sum]
  exact Finset.sum_congr rfl h

theorem realCoeff_X (j : Fin d) : RealCoeff (X j : MvPolynomial (Fin d) ℂ) := starP_X j

theorem eval_starP (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (starP p)
      = (starRingEnd ℂ) (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p) := by
  rw [starP, eval_map]
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

theorem inner_pgLp_pgLp (p q : MvPolynomial (Fin d) ℂ) :
    (inner ℂ (pgLp p) (pgLp q) : ℂ) = gaussInt (starP p * q) := by
  rw [inner_pgLp, gaussInt]
  refine integral_congr_ae ?_
  filter_upwards [pgLp_coeFn q] with x hx
  have hev : MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (starP p * q)
      = (starRingEnd ℂ) (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p)
        * MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) q := by
    rw [map_mul, eval_starP]
  rw [hx, hev, pgFun, pgFun, gaussWD_eq_sq]
  simp only [map_mul, Complex.conj_ofReal]
  push_cast
  ring

theorem PolySym.add {S T : Module.End ℂ (MvPolynomial (Fin d) ℂ)}
    (hS : PolySym S) (hT : PolySym T) : PolySym (S + T) := by
  intro p q
  simp only [LinearMap.add_apply, starP_add, add_mul, mul_add]
  rw [gaussInt_add, gaussInt_add, hS, hT]

theorem PolySym.real_smul {t : ℝ} {T : Module.End ℂ (MvPolynomial (Fin d) ℂ)} (hT : PolySym T) :
    PolySym (((t : ℂ)) • T) := by
  intro p q
  simp only [LinearMap.smul_apply, starP_real_smul, smul_mul_assoc, mul_smul_comm]
  rw [gaussInt_smul, gaussInt_smul, hT]

theorem PolyAdj.symm_of {S T : Module.End ℂ (MvPolynomial (Fin d) ℂ)}
    (h : PolyAdj S T) (h' : PolyAdj T S) : PolySym (S + T) := by
  intro p q
  simp only [LinearMap.add_apply, starP_add, add_mul, mul_add]
  rw [gaussInt_add, gaussInt_add, h, h']
  ring

theorem PolySym.comp_adj {S T : Module.End ℂ (MvPolynomial (Fin d) ℂ)}
    (hS : PolySym S) (hT : PolySym T) : PolyAdj (S.comp T) (T.comp S) := by
  intro p q
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hS, hT]

theorem weylProd_polySym {S T : Module.End ℂ (MvPolynomial (Fin d) ℂ)}
    (hS : PolySym S) (hT : PolySym T) : PolySym (weylProd S T) :=
  PolySym.real_smul ((hS.comp_adj hT).symm_of (hT.comp_adj hS))

@[simp] theorem mulOp_apply (f p : MvPolynomial (Fin d) ℂ) : mulOp f p = f * p := rfl

theorem mulOp_polySym {f : MvPolynomial (Fin d) ℂ} (hf : RealCoeff f) : PolySym (mulOp f) := by
  intro p q
  simp only [mulOp_apply, starP_mul, show starP f = f from hf]
  congr 1
  ring

theorem derOp_apply (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    derOp j p = pderiv j p - ((1 / 2 : ℝ) : ℂ) • (X j * p) := rfl

theorem momOp_apply (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    momOp j p = (-Complex.I) • (pderiv j p - ((1 / 2 : ℝ) : ℂ) • (X j * p)) := rfl

theorem starP_pderiv (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    starP (pderiv j p) = pderiv j (starP p) := (MvPolynomial.pderiv_map).symm

@[simp] theorem starP_neg (p : MvPolynomial (Fin d) ℂ) : starP (-p) = -starP p := map_neg _ _

@[simp] theorem starP_sub (p q : MvPolynomial (Fin d) ℂ) :
    starP (p - q) = starP p - starP q := map_sub _ _ _

theorem gaussInt_sub (r s : MvPolynomial (Fin d) ℂ) :
    gaussInt (r - s) = gaussInt r - gaussInt s := by
  have h := gaussInt_add r (-s)
  rw [show (-s) = (-1 : ℂ) • s by module, gaussInt_smul] at h
  rw [show r - s = r + (-1 : ℂ) • s by module, h]
  ring

theorem gaussInt_leibniz (j : Fin d) (P Q : MvPolynomial (Fin d) ℂ) :
    gaussInt (pderiv j P * Q) + gaussInt (P * pderiv j Q) = gaussInt (X j * (P * Q)) := by
  rw [← gaussInt_pderiv j (P * Q), ← gaussInt_add]
  congr 1
  rw [Derivation.leibniz]
  simp only [smul_eq_mul]
  ring

theorem starP_momOp (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    starP (momOp j p)
      = Complex.I • (pderiv j (starP p) - ((1 / 2 : ℝ) : ℂ) • (X j * starP p)) := by
  rw [momOp_apply, neg_smul, starP_neg, starP_smul, starP_sub, starP_pderiv, starP_real_smul,
    starP_mul, starP_X, Complex.conj_I, neg_smul, neg_neg]

theorem momOp_polySym (j : Fin d) : PolySym (momOp (d := d) j) := by
  intro p q
  have hleib := gaussInt_leibniz j (starP p) q
  have e1 : (X j : MvPolynomial (Fin d) ℂ) * starP p * q = X j * (starP p * q) := by ring
  have e2 : starP p * (X j * q) = X j * (starP p * q) := by ring
  have hL : gaussInt (starP (momOp j p) * q)
      = Complex.I * (gaussInt (pderiv j (starP p) * q)
          - ((1 / 2 : ℝ) : ℂ) * gaussInt (X j * (starP p * q))) := by
    rw [starP_momOp, smul_mul_assoc, gaussInt_smul, sub_mul, gaussInt_sub, smul_mul_assoc,
      gaussInt_smul, e1]
  have hR : gaussInt (starP p * momOp j q)
      = -Complex.I * (gaussInt (starP p * pderiv j q)
          - ((1 / 2 : ℝ) : ℂ) * gaussInt (X j * (starP p * q))) := by
    rw [momOp_apply, mul_smul_comm, gaussInt_smul, mul_sub, gaussInt_sub, mul_smul_comm,
      gaussInt_smul, e2]
  rw [hL, hR]
  push_cast
  linear_combination Complex.I * hleib

theorem commutator_coord_mom (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    mulOp (X j) (momOp j p) - momOp j (mulOp (X j) p) = Complex.I • p := by
  have hX : (pderiv j) (X j * p) = p + X j * pderiv j p := by
    rw [Derivation.leibniz]
    simp only [pderiv_X_self, smul_eq_mul, mul_one]
    ring
  simp only [mulOp_apply, momOp_apply, hX, neg_smul, smul_eq_C_mul]
  ring
section Transport
variable {D : Submodule ℂ (L2d d)}
theorem CoreRep.op_apply (Φ : CoreRep d D) (T : Module.End ℂ (MvPolynomial (Fin d) ℂ)) (x : D) :
    Φ.op T x = Φ.equiv (T (Φ.equiv.symm x)) := rfl

theorem CoreRep.coe_op (Φ : CoreRep d D) (T : Module.End ℂ (MvPolynomial (Fin d) ℂ)) (x : D) :
    ((Φ.op T x : D) : L2d d) = pgLp (T (Φ.equiv.symm x)) := by
  rw [CoreRep.op_apply, Φ.coe_equiv]

theorem CoreRep.coe_symm (Φ : CoreRep d D) (x : D) : ((x : D) : L2d d) = pgLp (Φ.equiv.symm x) := by
  rw [← Φ.coe_equiv (Φ.equiv.symm x), LinearEquiv.apply_symm_apply]

theorem CoreRep.symmetricOn_op (Φ : CoreRep d D) {T : Module.End ℂ (MvPolynomial (Fin d) ℂ)}
    (hT : PolySym T) : SymmetricOn D (D.subtype.comp (Φ.op T)) := by
  intro x y
  have hx : ((D.subtype.comp (Φ.op T)) x) = pgLp (T (Φ.equiv.symm x)) := Φ.coe_op T x
  have hy : ((D.subtype.comp (Φ.op T)) y) = pgLp (T (Φ.equiv.symm y)) := Φ.coe_op T y
  have hcx : ((x : D) : L2d d) = pgLp (Φ.equiv.symm x) := Φ.coe_symm x
  have hcy : ((y : D) : L2d d) = pgLp (Φ.equiv.symm y) := Φ.coe_symm y
  have e1 := inner_pgLp_pgLp (T (Φ.equiv.symm x)) (Φ.equiv.symm y)
  have e2 := inner_pgLp_pgLp (Φ.equiv.symm x) (T (Φ.equiv.symm y))
  rw [hx, hy, hcx, hcy, e1, e2]
  exact hT _ _

end Transport
section YangMills
variable {D : Submodule ℂ (L2d 99)}
theorem realCoeff_magPoly (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (i : Fin 3) (a : Fin 8) :
    RealCoeff (magPoly fabc i a) := by
  refine RealCoeff.sum fun j _ => RealCoeff.sum fun k _ => RealCoeff.smul ?_
  refine RealCoeff.add (realCoeff_X _) ?_
  exact RealCoeff.sum fun b _ => RealCoeff.sum fun c _ =>
    RealCoeff.smul ((realCoeff_X _).mul (realCoeff_X _))

theorem piOps_symmetricOn (Φ : CoreRep 99 D) (m : Fin 24) :
    SymmetricOn D (D.subtype.comp (piOps Φ m)) :=
  Φ.symmetricOn_op (momOp_polySym _)

theorem magOps_symmetricOn (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (m : Fin 24) :
    SymmetricOn D (D.subtype.comp (magOps Φ fabc m)) :=
  Φ.symmetricOn_op (mulOp_polySym (realCoeff_magPoly fabc _ _))

theorem ymHamiltonian_apply (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (x : D) :
    ymHamiltonian Φ fabc x
      = ((1 / 2 : ℝ) : ℂ)
        • ((∑ m, ((piOps Φ m (piOps Φ m x) : D) : L2d 99))
            + ∑ m, ((magOps Φ fabc m (magOps Φ fabc m x) : D) : L2d 99)) :=
  weylOp_apply _ _ x

theorem ymHamiltonian_symmetricOn (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) :
    SymmetricOn D (ymHamiltonian Φ fabc) :=
  weylOpDom_symmetricOn (piOps_symmetricOn Φ) (magOps_symmetricOn Φ fabc)

theorem ymHamiltonian_quadForm (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (x : D) :
    quadForm (ymHamiltonian Φ fabc) x
      = 1 / 2 * (∑ m, ‖((piOps Φ m x : D) : L2d 99)‖ ^ 2)
        + 1 / 2 * ∑ m, ‖((magOps Φ fabc m x : D) : L2d 99)‖ ^ 2 :=
  weylOpDom_quadForm (piOps_symmetricOn Φ) (magOps_symmetricOn Φ fabc) x

theorem ymHamiltonian_quadForm_nonneg (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ)
    (x : D) : 0 ≤ quadForm (ymHamiltonian Φ fabc) x :=
  weylOpDom_quadForm_nonneg (piOps_symmetricOn Φ) (magOps_symmetricOn Φ fabc) x

end YangMills
end BookProof.YangMillsHermite
namespace BookProof.HashimotoShiftInvert
open BookProof.FarisLavine
open Filter Topology
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}
@[simp] theorem shiftMap_apply (A : Dom →ₗ[ℂ] F) (γ : ℝ) (x : Dom) :
    shiftMap A γ x = A x + (γ : ℂ) • (x : F) := rfl

theorem norm_shiftMap_ge {A : Dom →ₗ[ℂ] F} (hpos : ∀ x : Dom, 0 ≤ quadForm A x)
    {γ : ℝ} (x : Dom) :
    γ * ‖(x : F)‖ ≤ ‖shiftMap A γ x‖ := by
  have hxy : (inner ℂ (x : F) (shiftMap A γ x) : ℂ).re = quadForm A x + γ * ‖(x : F)‖ ^ 2 := by
    simp only [shiftMap_apply, inner_add_right, inner_smul_right, Complex.add_re, quadForm]
    rw [inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  have h1 : γ * ‖(x : F)‖ ^ 2 ≤ (inner ℂ (x : F) (shiftMap A γ x) : ℂ).re := by
    rw [hxy]; linarith [hpos x]
  have h2 : (inner ℂ (x : F) (shiftMap A γ x) : ℂ).re ≤ ‖(x : F)‖ * ‖shiftMap A γ x‖ :=
    le_trans (Complex.re_le_norm _) (norm_inner_le_norm _ _)
  rcases eq_or_lt_of_le (norm_nonneg (x : F)) with h0 | hpx
  · rw [← h0]
    simp
  · nlinarith

theorem shiftMap_injective {A : Dom →ₗ[ℂ] F} (hpos : ∀ x : Dom, 0 ≤ quadForm A x)
    {γ : ℝ} (hγ : 0 < γ) : Function.Injective (shiftMap A γ) := by
  intro x y hxy
  have h : γ * ‖((x - y : Dom) : F)‖ ≤ ‖shiftMap A γ (x - y)‖ := norm_shiftMap_ge hpos _
  rw [map_sub, hxy, sub_self, norm_zero] at h
  have hx : ‖((x - y : Dom) : F)‖ = 0 := le_antisymm (by nlinarith) (norm_nonneg _)
  have : ((x - y : Dom) : F) = 0 := by simpa using hx
  have hz : x - y = 0 := Subtype.ext (by simpa using this)
  exact sub_eq_zero.mp hz

theorem IsShiftInvert.mem {A : Dom →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F}
    (h : IsShiftInvert A γ R) (u : F) : R u ∈ Dom := (h.2 u).choose

theorem IsShiftInvert.shift_apply {A : Dom →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F}
    (h : IsShiftInvert A γ R) (u : F) :
    A ⟨R u, h.mem u⟩ + (γ : ℂ) • R u = u := (h.2 u).choose_spec

theorem IsShiftInvert.isSelfAdjoint [CompleteSpace F] {A : Dom →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F}
    (h : IsShiftInvert A γ R) (hsym : SymmetricOn Dom A) : IsSelfAdjoint R := by
  refine ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr ?_
  intro u v
  have hu : A ⟨R u, h.mem u⟩ + (γ : ℂ) • R u = u := h.shift_apply u
  have hv : A ⟨R v, h.mem v⟩ + (γ : ℂ) • R v = v := h.shift_apply v
  have hcross : (inner ℂ (A ⟨R u, h.mem u⟩) (R v) : ℂ)
      = inner ℂ (R u) (A ⟨R v, h.mem v⟩) := hsym ⟨R u, h.mem u⟩ ⟨R v, h.mem v⟩
  have e1 : (inner ℂ (R u) v : ℂ)
      = inner ℂ (R u) (A ⟨R v, h.mem v⟩) + (γ : ℂ) * inner ℂ (R u) (R v) := by
    conv_lhs => rw [← hv]
    rw [inner_add_right, inner_smul_right]
  have e2 : (inner ℂ u (R v) : ℂ)
      = inner ℂ (A ⟨R u, h.mem u⟩) (R v) + (γ : ℂ) * inner ℂ (R u) (R v) := by
    conv_lhs => rw [← hu]
    rw [inner_add_left, inner_smul_left]
    simp
  change (inner ℂ (R u) v : ℂ) = inner ℂ u (R v)
  rw [e1, e2, hcross]

theorem IsShiftInvert.dom_eq_range {A : Dom →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F}
    (h : IsShiftInvert A γ R) : Dom = LinearMap.range (R : F →ₗ[ℂ] F) := by
  apply le_antisymm
  · intro x hx
    exact ⟨shiftMap A γ ⟨x, hx⟩, h.1 ⟨x, hx⟩⟩
  · rintro _ ⟨u, rfl⟩
    exact h.mem u

theorem exists_isShiftInvert {A : Dom →ₗ[ℂ] F} (hpos : ∀ x : Dom, 0 ≤ quadForm A x)
    {γ : ℝ} (hγ : 0 < γ) (hsurj : Function.Surjective (shiftMap A γ)) :
    ∃ R : F →L[ℂ] F, IsShiftInvert A γ R := by
  classical
  have hinj : Function.Injective (shiftMap A γ) := shiftMap_injective hpos hγ
  choose g hg using hsurj
  have hgshift : ∀ x : Dom, g (shiftMap A γ x) = x := fun x => hinj (hg _)
  have hadd : ∀ u v : F, ((g (u + v) : Dom) : F) = (g u : F) + (g v : F) := by
    intro u v
    have : shiftMap A γ (g (u + v)) = shiftMap A γ (g u + g v) := by
      rw [hg, map_add, hg, hg]
    exact congrArg Subtype.val (hinj this)
  have hsmul : ∀ (c : ℂ) (u : F), ((g (c • u) : Dom) : F) = c • (g u : F) := by
    intro c u
    have : shiftMap A γ (g (c • u)) = shiftMap A γ (c • g u) := by
      rw [hg, map_smul, hg]
    exact congrArg Subtype.val (hinj this)
  let L : F →ₗ[ℂ] F :=
    { toFun := fun u => (g u : F)
      map_add' := hadd
      map_smul' := by intro c u; simpa using hsmul c u }
  have hbound : ∀ u : F, ‖L u‖ ≤ γ⁻¹ * ‖u‖ := by
    intro u
    have hb : γ * ‖((g u : Dom) : F)‖ ≤ ‖shiftMap A γ (g u)‖ := norm_shiftMap_ge hpos _
    rw [hg u] at hb
    rw [inv_mul_eq_div, le_div_iff₀ hγ, mul_comm]
    exact hb
  refine ⟨L.mkContinuous γ⁻¹ hbound, fun x => ?_, fun u => ?_⟩
  · change ((g (shiftMap A γ x) : Dom) : F) = (x : F)
    rw [hgshift x]
  · refine ⟨(g u).2, ?_⟩
    have hsub : (⟨((g u : Dom) : F), (g u).2⟩ : Dom) = g u := Subtype.ext rfl
    change shiftMap A γ ⟨((g u : Dom) : F), _⟩ = u
    rw [hsub, hg u]
section Complete
variable [CompleteSpace F]
theorem shiftRange_isClosed {A : Dom →ₗ[ℂ] F} (hsym : SymmetricOn Dom A)
    (hpos : ∀ x : Dom, 0 ≤ quadForm A x)
    (hsa : ∀ w u : F, (∀ v : Dom, (inner ℂ (A v) w : ℂ) = inner ℂ (v : F) u) →
      ∃ h : w ∈ Dom, A ⟨w, h⟩ = u)
    {γ : ℝ} (hγ : 0 < γ) : IsClosed ((shiftRange A γ : Submodule ℂ F) : Set F) := by
  refine IsSeqClosed.isClosed ?_
  intro u p hu hup
  choose x hx using hu
  -- the preimages form a Cauchy sequence, by the shift bound
  have hcauchy : CauchySeq (fun n => ((x n : F))) := by
    have hucauchy : CauchySeq u := hup.cauchySeq
    rw [Metric.cauchySeq_iff] at hucauchy ⊢
    intro eps heps
    obtain ⟨N, hN⟩ := hucauchy (γ * eps) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hb : γ * ‖((x m - x n : Dom) : F)‖ ≤ ‖shiftMap A γ (x m - x n)‖ :=
      norm_shiftMap_ge hpos _
    rw [map_sub, hx m, hx n] at hb
    have hlt : ‖u m - u n‖ < γ * eps := by
      have hd := hN m hm n hn
      rwa [dist_eq_norm] at hd
    have hkey : γ * ‖((x m : F)) - ((x n : F))‖ < γ * eps := by
      refine lt_of_le_of_lt ?_ hlt
      simpa using hb
    rw [dist_eq_norm]
    exact lt_of_mul_lt_mul_left hkey hγ.le
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete hcauchy
  -- and their images under `A` converge too
  have hAconv : Tendsto (fun n => A (x n)) atTop (nhds (p - (γ : ℂ) • w)) := by
    have hval : ∀ n, A (x n) = u n - (γ : ℂ) • ((x n : F)) := by
      intro n
      have hn := hx n
      simp only [shiftMap_apply] at hn
      exact eq_sub_of_add_eq hn
    simp only [hval]
    exact hup.sub (hw.const_smul ((γ : ℂ)))
  obtain ⟨hwmem, hAw⟩ := closed_of_selfAdjointCriterion hsym hsa hw hAconv
  refine ⟨⟨w, hwmem⟩, ?_⟩
  simp only [shiftMap_apply, hAw]
  abel

theorem shiftRange_orthogonal_eq_bot {A : Dom →ₗ[ℂ] F}
    (hpos : ∀ x : Dom, 0 ≤ quadForm A x)
    (hsa : ∀ w u : F, (∀ v : Dom, (inner ℂ (A v) w : ℂ) = inner ℂ (v : F) u) →
      ∃ h : w ∈ Dom, A ⟨w, h⟩ = u)
    {γ : ℝ} (hγ : 0 < γ) : (shiftRange A γ)ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro w hw
  have hip : ∀ v : Dom, (inner ℂ (A v) w : ℂ) = inner ℂ (v : F) (-(γ : ℂ) • w) := by
    intro v
    have hmem : shiftMap A γ v ∈ shiftRange A γ := ⟨v, rfl⟩
    have h0 : (inner ℂ (shiftMap A γ v) w : ℂ) = 0 := hw _ hmem
    rw [shiftMap_apply, inner_add_left, inner_smul_left, Complex.conj_ofReal] at h0
    rw [inner_smul_right]
    have hval : (inner ℂ (A v) w : ℂ) = -((γ : ℂ) * inner ℂ ((v : F)) w) := by
      linear_combination h0
    rw [hval]
    ring
  obtain ⟨hwmem, hAw⟩ := hsa w (-(γ : ℂ) • w) hip
  have hquad : quadForm A ⟨w, hwmem⟩ = -γ * ‖w‖ ^ 2 := by
    rw [quadForm, hAw, inner_smul_right, inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  have h1 := hpos ⟨w, hwmem⟩
  rw [hquad] at h1
  have hzero : ‖w‖ = 0 := by
    by_contra hne
    have hpw : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg w) (Ne.symm hne)
    have hcontr : 0 < γ * ‖w‖ ^ 2 := by positivity
    linarith
  simpa using hzero

theorem shiftMap_surjective {A : Dom →ₗ[ℂ] F} (hsym : SymmetricOn Dom A)
    (hpos : ∀ x : Dom, 0 ≤ quadForm A x)
    (hsa : ∀ w u : F, (∀ v : Dom, (inner ℂ (A v) w : ℂ) = inner ℂ (v : F) u) →
      ∃ h : w ∈ Dom, A ⟨w, h⟩ = u)
    {γ : ℝ} (hγ : 0 < γ) : Function.Surjective (shiftMap A γ) := by
  have hclosed : IsClosed ((shiftRange A γ : Submodule ℂ F) : Set F) :=
    shiftRange_isClosed hsym hpos hsa hγ
  haveI : CompleteSpace (shiftRange A γ) := hclosed.completeSpace_coe
  have htop : shiftRange A γ = ⊤ := by
    have h1 := Submodule.orthogonal_orthogonal (shiftRange A γ)
    rw [shiftRange_orthogonal_eq_bot hpos hsa hγ, Submodule.bot_orthogonal_eq_top] at h1
    exact h1.symm
  intro u
  have hmem : u ∈ shiftRange A γ := by rw [htop]; trivial
  exact hmem

end Complete
end BookProof.HashimotoShiftInvert
namespace BookProof.ChapterH9
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem norm_sub_starProjection_le (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (u w : E) (hw : w ∈ K) : ‖u - K.starProjection u‖ ≤ ‖u - w‖ := by
  rw [Submodule.starProjection_minimal]
  refine ciInf_le_of_le ⟨0, ?_⟩ (⟨w, hw⟩ : K) le_rfl
  rintro r ⟨x, rfl⟩
  positivity

end BookProof.ChapterH9
namespace BookProof.HermiteGalerkin
open Filter Topology
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
theorem starProjection_tendsto_of_monotone_dense (K : ℕ → Submodule ℂ F)
    [∀ n, (K n).HasOrthogonalProjection] (hmono : Monotone K)
    (hdense : Dense ((⨆ n : ℕ, K n : Submodule ℂ F) : Set F)) (u : F) :
    Tendsto (fun n : ℕ => (K n).starProjection u) atTop (nhds u) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  rw [Metric.tendsto_atTop]
  intro eps heps
  obtain ⟨w, hw, hwd⟩ := hdense.exists_dist_lt u heps
  obtain ⟨N, hN⟩ := (Submodule.mem_iSup_of_directed _ hmono.directed_le).mp hw
  refine ⟨N, fun n hn => ?_⟩
  have h1 : ‖u - (K n).starProjection u‖ ≤ ‖u - w‖ :=
    BookProof.ChapterH9.norm_sub_starProjection_le _ u w (hmono hn hN)
  have h2 : ‖u - w‖ < eps := by simpa [dist_eq_norm] using hwd
  have h3 : ‖(K n).starProjection u - u‖ = ‖u - (K n).starProjection u‖ := norm_sub_rev _ _
  simp only [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _), h3]
  exact lt_of_le_of_lt h1 h2

theorem compression_tendsto_of_starProjection_tendsto (K : ℕ → Submodule ℂ F)
    [∀ n, (K n).HasOrthogonalProjection] (A : F →L[ℂ] F)
    (hP : ∀ u : F, Tendsto (fun n : ℕ => (K n).starProjection u) atTop (nhds u)) (u : F) :
    Tendsto (fun n : ℕ => (K n).starProjection (A ((K n).starProjection u)))
      atTop (nhds (A u)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbound : ∀ n : ℕ, ‖(K n).starProjection (A ((K n).starProjection u)) - A u‖
      ≤ ‖A‖ * ‖(K n).starProjection u - u‖ + ‖(K n).starProjection (A u) - A u‖ := by
    intro n
    have hsplit : (K n).starProjection (A ((K n).starProjection u)) - A u
        = (K n).starProjection (A ((K n).starProjection u) - A u)
          + ((K n).starProjection (A u) - A u) := by
      simp only [map_sub]
      abel
    rw [hsplit]
    refine le_trans (norm_add_le _ _) ?_
    gcongr
    refine le_trans ((K n).norm_starProjection_apply_le _) ?_
    have hAsub : A ((K n).starProjection u) - A u = A ((K n).starProjection u - u) := by
      rw [map_sub]
    rw [hAsub]
    exact A.le_opNorm _
  have h1 : Tendsto (fun n : ℕ => ‖A‖ * ‖(K n).starProjection u - u‖) atTop (nhds 0) := by
    have := hP u
    rw [tendsto_iff_norm_sub_tendsto_zero] at this
    simpa using this.const_mul ‖A‖
  have h2 : Tendsto (fun n : ℕ => ‖(K n).starProjection (A u) - A u‖) atTop (nhds 0) := by
    have := hP (A u)
    rw [tendsto_iff_norm_sub_tendsto_zero] at this
    simpa using this
  exact squeeze_zero (fun n => norm_nonneg _) hbound (by simpa using h1.add h2)

theorem galerkinSpan_mono (b : HilbertBasis ℕ ℂ F) {m n : ℕ} (hmn : m ≤ n) :
    galerkinSpan b m ≤ galerkinSpan b n :=
  Submodule.span_mono (Set.image_mono fun _ hi => lt_of_lt_of_le hi hmn)

theorem basis_mem_galerkinSpan (b : HilbertBasis ℕ ℂ F) {i m : ℕ} (him : i < m) :
    b i ∈ galerkinSpan b m :=
  Submodule.subset_span ⟨i, him, rfl⟩

theorem galerkinSpan_le_finiteModeDomain (b : HilbertBasis ℕ ℂ F) (m : ℕ) :
    galerkinSpan b m ≤ finiteModeDomain b :=
  Submodule.span_mono (by rintro x ⟨i, _, rfl⟩; exact ⟨i, rfl⟩)

theorem finiteModeDomain_eq_iSup (b : HilbertBasis ℕ ℂ F) :
    finiteModeDomain b = ⨆ m : ℕ, galerkinSpan b m := by
  refine le_antisymm ?_ (iSup_le fun m => galerkinSpan_le_finiteModeDomain b m)
  rw [finiteModeDomain, Submodule.span_le]
  rintro x ⟨i, rfl⟩
  exact Submodule.mem_iSup_of_mem (i + 1) (basis_mem_galerkinSpan b (Nat.lt_succ_self i))

theorem exists_mem_galerkinSpan (b : HilbertBasis ℕ ℂ F) {x : F} (hx : x ∈ finiteModeDomain b) :
    ∃ m : ℕ, x ∈ galerkinSpan b m := by
  rw [finiteModeDomain_eq_iSup] at hx
  have hmono : Monotone (fun m : ℕ => galerkinSpan b m) := fun _ _ h => galerkinSpan_mono b h
  have hdir : Directed (· ≤ ·) (fun m : ℕ => galerkinSpan b m) := hmono.directed_le
  exact (Submodule.mem_iSup_of_directed _ hdir).mp hx

theorem finiteModeDomain_dense (b : HilbertBasis ℕ ℂ F) :
    Dense ((finiteModeDomain b : Submodule ℂ F) : Set F) :=
  Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span

theorem galerkinSpan_iSup_dense (b : HilbertBasis ℕ ℂ F) :
    Dense ((⨆ m : ℕ, galerkinSpan b m : Submodule ℂ F) : Set F) := by
  rw [← finiteModeDomain_eq_iSup]
  exact finiteModeDomain_dense b

theorem galerkinProj_tendsto (b : HilbertBasis ℕ ℂ F) (u : F) :
    Tendsto (fun m : ℕ => (galerkinSpan b m).starProjection u) atTop (nhds u) :=
  starProjection_tendsto_of_monotone_dense _ (fun _ _ h => galerkinSpan_mono b h)
    (galerkinSpan_iSup_dense b) u

@[simp] theorem galerkinCompression_apply (A : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F) (m : ℕ)
    (u : F) : galerkinCompression A b m u
      = (galerkinSpan b m).starProjection (A ((galerkinSpan b m).starProjection u)) := rfl

theorem galerkinCompression_tendsto (A : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F) (u : F) :
    Tendsto (fun m : ℕ => galerkinCompression A b m u) atTop (nhds (A u)) :=
  compression_tendsto_of_starProjection_tendsto _ A (galerkinProj_tendsto b) u
end BookProof.HermiteGalerkin

namespace BookProof.HashimotoShiftInvert
open BookProof.FarisLavine
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}
theorem IsShiftInvert.norm_apply_le {A : Dom →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F}
    (h : IsShiftInvert A γ R) (hpos : ∀ x : Dom, 0 ≤ quadForm A x) (hγ : 0 < γ) (u : F) :
    ‖R u‖ ≤ γ⁻¹ * ‖u‖ := by
  have hb : γ * ‖((⟨R u, h.mem u⟩ : Dom) : F)‖ ≤ ‖shiftMap A γ ⟨R u, h.mem u⟩‖ :=
    norm_shiftMap_ge hpos _
  rw [show shiftMap A γ ⟨R u, h.mem u⟩ = u from h.shift_apply u] at hb
  rw [inv_mul_eq_div, le_div_iff₀ hγ, mul_comm]
  simpa using hb

theorem IsShiftInvert.inner_nonneg {A : Dom →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F}
    (h : IsShiftInvert A γ R) (hpos : ∀ x : Dom, 0 ≤ quadForm A x) (hγ : 0 < γ) (u : F) :
    0 ≤ (inner ℂ u (R u) : ℂ).re := by
  have hu : A ⟨R u, h.mem u⟩ + (γ : ℂ) • R u = u := h.shift_apply u
  have key : ∀ (y : F) (hy : y ∈ Dom),
      (inner ℂ (A ⟨y, hy⟩ + (γ : ℂ) • y) y : ℂ).re = quadForm A ⟨y, hy⟩ + γ * ‖y‖ ^ 2 := by
    intro y hy
    have hq : (inner ℂ (A ⟨y, hy⟩) y : ℂ).re = quadForm A ⟨y, hy⟩ := by
      rw [quadForm, ← inner_conj_symm (A ⟨y, hy⟩) y, Complex.conj_re]
    rw [inner_add_left, inner_smul_left, Complex.add_re, hq, inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  have hexp := key (R u) (h.mem u)
  rw [hu] at hexp
  rw [hexp]
  have := hpos ⟨R u, h.mem u⟩
  positivity

end BookProof.HashimotoShiftInvert

namespace OtherYmGeometry
open BookProof.ChapterH4 BookProof.ChapterH9
variable {F E : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem krylov_rayleigh_transfer (V : F →L[ℂ] E) (X : E →L[ℂ] E) (y : F) :
    inner ℂ y (compress V X y) = inner ℂ (V y) (X (V y)) := by
  rw [compress]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  exact ContinuousLinearMap.adjoint_inner_right V y (X (V y))
theorem numRange_compress_subset (V : F →L[ℂ] E) (X : E →L[ℂ] E)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖) : numRange (compress V X) ⊆ numRange X := by
  rintro c ⟨y, hy, rfl⟩
  exact ⟨V y, by rw [hViso, hy], (krylov_rayleigh_transfer V X y).symm⟩
theorem crouzeix_domain_transfer (V : F →L[ℂ] E) (X : E →L[ℂ] E)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖) (S : Set ℂ) (hconv : Convex ℝ S)
    (hS : numRange X ⊆ S) :
    (convexHull ℝ) (numRange (compress V X)) ⊆ S :=
  convexHull_min ((numRange_compress_subset V X hViso).trans hS) hconv

end OtherYmGeometry
namespace OtherYmGeometry
open BookProof.ChapterSirkSpectralGeometry
open BookProof.ChapterH4 BookProof.ChapterH6 BookProof.ChapterH9
open BookProof.ChapterSirkEndToEnd BookProof.HashimotoShiftInvert BookProof.FarisLavine
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {Dom : Submodule ℂ F}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
theorem convex_realSegment (a b : ℝ) : Convex ℝ (realSegment a b) := by
  rintro x ⟨hxi, hxl, hxu⟩ y ⟨hyi, hyl, hyu⟩ s t hs ht hst
  have him : (s • x + t • y : ℂ).im = 0 := by
    simp [Complex.real_smul, hxi, hyi]
  have hre : (s • x + t • y : ℂ).re = s * x.re + t * y.re := by
    simp [Complex.real_smul, Complex.mul_re, hxi, hyi]
  have hsa : s * a + t * a = a := by rw [← add_mul, hst, one_mul]
  have hsb : s * b + t * b = b := by rw [← add_mul, hst, one_mul]
  refine ⟨him, ?_, ?_⟩ <;> rw [hre]
  · linarith [mul_le_mul_of_nonneg_left hxl hs, mul_le_mul_of_nonneg_left hyl ht]
  · linarith [mul_le_mul_of_nonneg_left hxu hs, mul_le_mul_of_nonneg_left hyu ht]
theorem numRange_subset_realSegment_of_shiftInvert {A : Dom →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F}
    (hR : IsShiftInvert A γ R) (hsym : SymmetricOn Dom A)
    (hpos : ∀ x : Dom, 0 ≤ quadForm A x) (hγ : 0 < γ) :
    numRange R ⊆ realSegment 0 γ⁻¹ := by
  rintro c ⟨x, hx, rfl⟩
  have hsa : IsSelfAdjoint R := hR.isSelfAdjoint hsym
  have hsymm : ∀ u v : F, (inner ℂ (R u) v : ℂ) = inner ℂ u (R v) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsa
  refine ⟨?_, ?_, ?_⟩
  · have h1 : (starRingEnd ℂ) (inner ℂ x (R x) : ℂ) = (inner ℂ x (R x) : ℂ) := by
      rw [inner_conj_symm, hsymm x x]
    have := Complex.conj_eq_iff_im.mp h1
    simpa using this
  · simpa using hR.inner_nonneg hpos hγ x
  · have hR' : ‖R x‖ ≤ γ⁻¹ * ‖x‖ := hR.norm_apply_le hpos hγ x
    calc (inner ℂ x (R x) : ℂ).re
        ≤ ‖(inner ℂ x (R x) : ℂ)‖ := Complex.re_le_norm _
      _ ≤ ‖x‖ * ‖R x‖ := norm_inner_le_norm _ _
      _ ≤ γ⁻¹ := by rw [hx, one_mul]; simpa [hx] using hR'
theorem crouzeix_domain_shiftInvert {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [CompleteSpace G] {A : Dom →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F}
    (hR : IsShiftInvert A γ R) (hsym : SymmetricOn Dom A)
    (hpos : ∀ x : Dom, 0 ≤ quadForm A x) (hγ : 0 < γ)
    (V : G →L[ℂ] F) (hViso : ∀ x : G, ‖V x‖ = ‖x‖) :
    convexHull ℝ (numRange (compress V R)) ⊆ realSegment 0 γ⁻¹ :=
  crouzeix_domain_transfer V R hViso _ (convex_realSegment 0 γ⁻¹)
    (numRange_subset_realSegment_of_shiftInvert hR hsym hpos hγ)

end OtherYmGeometry

-- Generated from ChapterSirkPerSystem.lean — theorem BookProof.ChapterSirkPerSystem.ym_sirk_crouzeix_domain
open BookProof.ChapterSirkPerSystem











open BookProof.ChapterH4 BookProof.ChapterH9 BookProof.ChapterSirkSpectralGeometry
open BookProof.HashimotoShiftInvert BookProof.FarisLavine BookProof.EsaClosure
open BookProof.YangMillsFriedrichs BookProof.YangMillsHermite BookProof.HermiteProductCore
open BookProof.Starobinsky
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LpNat
open BookProof.NavierStokesFlow.ThreeComponent
open BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.NSHashimoto
open BookProof.NavierStokesFlow.DiffHashimoto BookProof.NavierStokesFlow.DifferentialL2
open BookProof.NavierStokesFlow.LagrangianEsa BookProof.NavierStokesFlow.LagrangianKatoRellich
open BookProof.HermiteGalerkin
theorem solution (e : ℕ ≃ (Fin 99 →₀ ℕ))
    (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) {γ : ℝ} (hγ : 0 < γ) :
    ∃ (Dom : Submodule ℂ (L2d 99)) (A : Dom →ₗ[ℂ] L2d 99) (R : L2d 99 →L[ℂ] L2d 99),
      IsPositiveSelfAdjointExtension (ymHamiltonian (coreRepBasis e) fabc) A ∧
        IsShiftInvert A γ R ∧ IsSelfAdjoint R ∧
        numRange R ⊆ realSegment 0 γ⁻¹ ∧
        ∀ (m : ℕ) (V : EuclideanSpace ℂ (Fin m) →L[ℂ] L2d 99),
          (∀ x, ‖V x‖ = ‖x‖) →
            convexHull ℝ (numRange (compress V R)) ⊆ realSegment 0 γ⁻¹ := by
  obtain ⟨Dom, A, hA⟩ := SirkFriedrichsAux.friedrichs_extension_exists
    ⟨finiteModeDomain (coreBasis e), ymHamiltonian (coreRepBasis e) fabc,
      ymHamiltonian_symmetricOn _ fabc, ymHamiltonian_quadForm_nonneg _ fabc⟩
    (finiteModeDomain_dense (coreBasis e))
  obtain ⟨R, hR⟩ := exists_isShiftInvert hA.2.2.1 hγ
    (shiftMap_surjective hA.2.1 hA.2.2.1 hA.2.2.2 hγ)
  exact ⟨Dom, A, R, hA, hR, hR.isSelfAdjoint hA.2.1,
    OtherYmGeometry.numRange_subset_realSegment_of_shiftInvert hR hA.2.1 hA.2.2.1 hγ,
    fun _ V hV => OtherYmGeometry.crouzeix_domain_shiftInvert hR hA.2.1 hA.2.2.1 hγ V hV⟩
#print axioms solution

example : (∀ (e : ℕ ≃ (Fin 99 →₀ ℕ))
    (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) {γ : ℝ} (hγ : 0 < γ) , 
    ∃ (Dom : Submodule ℂ (L2d 99)) (A : Dom →ₗ[ℂ] L2d 99) (R : L2d 99 →L[ℂ] L2d 99),
      IsPositiveSelfAdjointExtension (ymHamiltonian (coreRepBasis e) fabc) A ∧
        IsShiftInvert A γ R ∧ IsSelfAdjoint R ∧
        numRange R ⊆ realSegment 0 γ⁻¹ ∧
        ∀ (m : ℕ) (V : EuclideanSpace ℂ (Fin m) →L[ℂ] L2d 99),
          (∀ x, ‖V x‖ = ‖x‖) →
            convexHull ℝ (numRange (compress V R)) ⊆ realSegment 0 γ⁻¹) := @solution
