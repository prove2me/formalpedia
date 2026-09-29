-- Prove2me | solution 2 for BookProof.FockSecondQuantization.secondQuantization_friedrichs
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T16:41:03.975986+00:00
-- url     : https://prove2.me/submissions/c19beb97-9a29-4a2f-97c3-1ff95a453ad2

/- Adapted from Leonardo Pedro, timepiece commit 61595bc, Apache-2.0.
https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean
The form-completion construction is adapted from ChapterFriedrichsExtension.lean;
Yang–Mills core positivity and symmetry from ChapterYangMillsHermite.lean, same revision. -/
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
set_option autoImplicit false
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
namespace SirkFriedrichsAux
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert
open BookProof.FriedrichsExtension BookProof.FriedrichsExtension.FormDom
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
theorem friedrichs_extension_of_semibounded_below {D : Submodule ℂ F} (H : D →ₗ[ℂ] F)
    (hdense : Dense (D : Set F)) (hsym : SymmetricOn D H) (c : ℝ)
    (hbelow : ∀ x : D, -c * ‖(x : F)‖ ^ 2 ≤ quadForm H x) :
    ∃ (Dom : Submodule ℂ F) (A : Dom →ₗ[ℂ] F), IsSemiboundedSelfAdjointExtension c H A := by
  -- the shifted operator `H + c` is positive
  set Hc : D →ₗ[ℂ] F := H + (c : ℂ) • D.subtype with hHc
  have hshift : ∀ x : D, quadForm Hc x = quadForm H x + c * ‖(x : F)‖ ^ 2 := by
    intro x
    simp only [hHc, quadForm, LinearMap.add_apply, LinearMap.smul_apply, Submodule.subtype_apply,
      inner_add_right, inner_smul_right, Complex.add_re]
    congr 1
    rw [inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  have hcsym : SymmetricOn D Hc := by
    intro x y
    simp only [hHc, LinearMap.add_apply, LinearMap.smul_apply, Submodule.subtype_apply,
      inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    rw [hsym x y]
  have hcpos : ∀ x : D, 0 ≤ quadForm Hc x := by
    intro x
    rw [hshift]
    linarith [hbelow x]
  obtain ⟨Dom, A', hA'⟩ := friedrichs_extension_exists ⟨D, Hc, hcsym, hcpos⟩ hdense
  obtain ⟨hagree, hsymA, hposA, hsa⟩ := hA'
  refine ⟨Dom, A' - (c : ℂ) • Dom.subtype, ?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨h, hx⟩ := hagree x
    refine ⟨h, ?_⟩
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Submodule.subtype_apply, hx, hHc,
      LinearMap.add_apply]
    module
  · intro x y
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Submodule.subtype_apply,
      inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    rw [hsymA x y]
  · intro y
    have h : quadForm (A' - (c : ℂ) • Dom.subtype) y = quadForm A' y - c * ‖(y : F)‖ ^ 2 := by
      simp only [quadForm, LinearMap.sub_apply, LinearMap.smul_apply, Submodule.subtype_apply,
        inner_sub_right, inner_smul_right, Complex.sub_re]
      congr 1
      rw [inner_self_eq_norm_sq_to_K]
      simp [← Complex.ofReal_pow]
    rw [h]
    linarith [hposA y]
  · intro w u hw
    have hw' : ∀ v : Dom, (inner ℂ (A' v) w : ℂ) = inner ℂ (v : F) (u + (c : ℂ) • w) := by
      intro v
      have := hw v
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Submodule.subtype_apply,
        inner_sub_left, inner_smul_left, Complex.conj_ofReal] at this
      rw [inner_add_right, inner_smul_right, ← this]
      ring
    obtain ⟨h, hval⟩ := hsa w (u + (c : ℂ) • w) hw'
    refine ⟨h, ?_⟩
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Submodule.subtype_apply, hval]
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

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert
noncomputable section
@[simp] theorem up_self (j : ℕ) (α : Conf) : up j α j = α j + 1 := by
  simp [up]

theorem up_of_ne {i j : ℕ} (α : Conf) (h : i ≠ j) : up j α i = α i := by
  simp [up, Finsupp.update_apply, h]

@[simp] theorem dn_self (j : ℕ) (α : Conf) : dn j α j = α j - 1 := by
  simp [dn]

theorem dn_of_ne {i j : ℕ} (α : Conf) (h : i ≠ j) : dn j α i = α i := by
  simp [dn, Finsupp.update_apply, h]

@[simp] theorem dn_up (j : ℕ) (α : Conf) : dn j (up j α) = α := by
  refine Finsupp.ext fun i => ?_
  by_cases h : i = j
  · subst h; simp
  · rw [dn_of_ne _ h, up_of_ne _ h]

theorem up_dn (j : ℕ) {α : Conf} (h : 1 ≤ α j) : up j (dn j α) = α := by
  refine Finsupp.ext fun i => ?_
  by_cases hi : i = j
  · subst hi; simp; omega
  · rw [up_of_ne _ hi, dn_of_ne _ hi]

theorem up_injective (j : ℕ) : Function.Injective (up j) := by
  intro α β h
  have := congrArg (dn j) h
  simpa using this

theorem support_up (j : ℕ) (α : Conf) : (up j α).support ⊆ insert j α.support := by
  intro i hi
  by_cases h : i = j
  · simp [h]
  · have : α i ≠ 0 := by
      have := Finsupp.mem_support_iff.mp hi
      rwa [up_of_ne _ h] at this
    exact Finset.mem_insert_of_mem (Finsupp.mem_support_iff.mpr this)

theorem support_dn (j : ℕ) (α : Conf) : (dn j α).support ⊆ α.support := by
  intro i hi
  have hi' := Finsupp.mem_support_iff.mp hi
  by_cases h : i = j
  · subst h
    rw [dn_self] at hi'
    exact Finsupp.mem_support_iff.mpr (by omega)
  · rw [dn_of_ne _ h] at hi'
    exact Finsupp.mem_support_iff.mpr hi'

@[simp] theorem annA_single (j : ℕ) (β : Conf) (c : ℂ) :
    annA j (Finsupp.single β c) = c • Finsupp.single (dn j β) ((Real.sqrt (β j) : ℝ) : ℂ) := by
  simp [annA, LinearMap.toSpanSingleton]

@[simp] theorem creA_single (j : ℕ) (β : Conf) (c : ℂ) :
    creA j (Finsupp.single β c)
      = c • Finsupp.single (up j β) ((Real.sqrt ((β j : ℝ) + 1) : ℝ) : ℂ) := by
  simp [creA, LinearMap.toSpanSingleton]

theorem annA_apply (j : ℕ) (u : FockAlg) (α : Conf) :
    annA j u α = ((Real.sqrt ((α j : ℝ) + 1) : ℝ) : ℂ) * u (up j α) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg]; ring
  | single β c =>
    rw [annA_single]
    by_cases hb : β = up j α
    · subst hb
      simp [mul_comm]
    · have h1 : (Finsupp.single β c : FockAlg) (up j α) = 0 := by
        simp [Ne.symm hb]
      rw [h1, mul_zero]
      by_cases hj : β j = 0
      · simp [hj]
      · have hne : dn j β ≠ α := by
          intro hc
          exact hb (by rw [← hc, up_dn j (by omega)])
        simp [hne]

theorem creA_apply (j : ℕ) (u : FockAlg) (α : Conf) :
    creA j u α = ((Real.sqrt (α j) : ℝ) : ℂ) * u (dn j α) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg]; ring
  | single β c =>
    rw [creA_single]
    by_cases hb : β = dn j α
    · subst hb
      by_cases hj : 1 ≤ α j
      · rw [up_dn j hj]
        have hcast : ((α j - 1 : ℕ) : ℝ) + 1 = (α j : ℝ) := by
          rw [Nat.cast_sub (R := ℝ) hj]; ring
        simp only [dn_self, hcast, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul]
        rw [mul_comm]
      · have h0 : α j = 0 := by omega
        have hne : up j (dn j α) ≠ α := by
          intro hc
          have := congrArg (fun f : Conf => f j) hc
          simp at this
          omega
        simp [hne, h0]
    · have h1 : (Finsupp.single β c : FockAlg) (dn j α) = 0 := by
        simp [Ne.symm hb]
      rw [h1, mul_zero]
      have hne : up j β ≠ α := by
        intro hc
        exact hb (by rw [← hc, dn_up])
      simp [hne]

theorem ccr_annA_creA (j : ℕ) (u : FockAlg) : annA j (creA j u) - creA j (annA j u) = u := by
  refine Finsupp.ext fun α => ?_
  rw [Finsupp.sub_apply, annA_apply, creA_apply, creA_apply, annA_apply, up_self, dn_up]
  by_cases hj : 1 ≤ α j
  · have hcast : ((dn j α) j : ℝ) + 1 = (α j : ℝ) := by
      rw [dn_self, Nat.cast_sub (R := ℝ) hj]; ring
    rw [hcast, up_dn j hj]
    push_cast
    have h1 : ((Real.sqrt ((α j : ℝ) + 1) : ℝ) : ℂ) * ((Real.sqrt ((α j : ℝ) + 1) : ℝ) : ℂ)
        = ((α j : ℝ) : ℂ) + 1 := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
      push_cast
      ring
    have h2 : ((Real.sqrt ((α j : ℝ)) : ℝ) : ℂ) * ((Real.sqrt ((α j : ℝ)) : ℝ) : ℂ)
        = ((α j : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    linear_combination (u α) * h1 - (u α) * h2
  · have h0 : α j = 0 := by omega
    rw [h0]
    norm_num

theorem up_dn_comm {j k : ℕ} (h : j ≠ k) (α : Conf) : dn k (up j α) = up j (dn k α) := by
  refine Finsupp.ext fun i => ?_
  by_cases hik : i = k
  · subst hik
    rw [dn_self, up_of_ne _ h.symm, up_of_ne _ h.symm, dn_self]
  · by_cases hij : i = j
    · subst hij
      rw [dn_of_ne _ hik, up_self, up_self, dn_of_ne _ hik]
    · rw [dn_of_ne _ hik, up_of_ne _ hij, up_of_ne _ hij, dn_of_ne _ hik]

theorem dn_dn_comm (j k : ℕ) (α : Conf) : dn k (dn j α) = dn j (dn k α) := by
  rcases eq_or_ne j k with rfl | h
  · rfl
  refine Finsupp.ext fun i => ?_
  by_cases hik : i = k
  · subst hik
    rw [dn_self, dn_of_ne _ h.symm, dn_of_ne _ h.symm, dn_self]
  · by_cases hij : i = j
    · subst hij
      rw [dn_of_ne _ hik, dn_self, dn_self, dn_of_ne _ hik]
    · rw [dn_of_ne _ hik, dn_of_ne _ hij, dn_of_ne _ hij, dn_of_ne _ hik]

theorem up_up_comm (j k : ℕ) (α : Conf) : up k (up j α) = up j (up k α) := by
  rcases eq_or_ne j k with rfl | h
  · rfl
  refine Finsupp.ext fun i => ?_
  by_cases hik : i = k
  · subst hik
    rw [up_self, up_of_ne _ h.symm, up_of_ne _ h.symm, up_self]
  · by_cases hij : i = j
    · subst hij
      rw [up_of_ne _ hik, up_self, up_self, up_of_ne _ hik]
    · rw [up_of_ne _ hik, up_of_ne _ hij, up_of_ne _ hij, up_of_ne _ hik]

theorem ccr_annA_creA_of_ne {j k : ℕ} (h : j ≠ k) (u : FockAlg) :
    annA j (creA k u) = creA k (annA j u) := by
  refine Finsupp.ext fun α => ?_
  rw [annA_apply, creA_apply, creA_apply, annA_apply, up_of_ne _ h.symm, dn_of_ne _ h,
    up_dn_comm h]
  ring

theorem ccr_annA_annA (j k : ℕ) (u : FockAlg) : annA j (annA k u) = annA k (annA j u) := by
  refine Finsupp.ext fun α => ?_
  rcases eq_or_ne j k with rfl | h
  · rfl
  rw [annA_apply, annA_apply, annA_apply, annA_apply, up_of_ne _ h.symm, up_of_ne _ h,
    up_up_comm]
  ring

theorem ccr_creA_creA (j k : ℕ) (u : FockAlg) : creA j (creA k u) = creA k (creA j u) := by
  refine Finsupp.ext fun α => ?_
  rcases eq_or_ne j k with rfl | h
  · rfl
  rw [creA_apply, creA_apply, creA_apply, creA_apply, dn_of_ne _ h.symm, dn_of_ne _ h,
    dn_dn_comm]
  ring

theorem support_annA (j : ℕ) (u : FockAlg) : (annA j u).support ⊆ u.support.image (dn j) := by
  intro α hα
  have hα' := Finsupp.mem_support_iff.mp hα
  rw [annA_apply] at hα'
  have hu : u (up j α) ≠ 0 := fun h => hα' (by rw [h, mul_zero])
  exact Finset.mem_image.mpr ⟨up j α, Finsupp.mem_support_iff.mpr hu, by simp⟩

theorem support_creA (j : ℕ) (u : FockAlg) : (creA j u).support ⊆ u.support.image (up j) := by
  intro α hα
  have hα' := Finsupp.mem_support_iff.mp hα
  rw [creA_apply] at hα'
  have hu : u (dn j α) ≠ 0 := fun h => hα' (by rw [h, mul_zero])
  have hj : 1 ≤ α j := by
    by_contra hc
    have h0 : α j = 0 := by omega
    exact hα' (by rw [h0]; norm_num)
  exact Finset.mem_image.mpr ⟨dn j α, Finsupp.mem_support_iff.mpr hu, up_dn j hj⟩

theorem support_subset_modes {u : FockAlg} {β : Conf} (h : β ∈ u.support) :
    β.support ⊆ modes u := fun _ hi => Finset.mem_biUnion.mpr ⟨β, h, hi⟩

theorem annA_eq_zero_of_not_mem_modes {u : FockAlg} {k : ℕ} (h : k ∉ modes u) :
    annA k u = 0 := by
  refine Finsupp.ext fun α => ?_
  rw [annA_apply, Finsupp.zero_apply]
  have hu : u (up k α) = 0 := by
    by_contra hc
    refine h (support_subset_modes (Finsupp.mem_support_iff.mpr hc) ?_)
    exact Finsupp.mem_support_iff.mpr (by rw [up_self]; omega)
  rw [hu, mul_zero]

@[simp] theorem toLp_apply (u : FockAlg) (α : Conf) : ((toLp u : Fock) : Conf → ℂ) α = u α := rfl

@[simp] theorem toLpL_apply (u : FockAlg) : toLpL u = toLp u := rfl

theorem inner_toLp_of_subset {u : FockAlg} {s : Finset Conf} (hs : u.support ⊆ s)
    (v : FockAlg) :
    (inner ℂ (toLp u) (toLp v) : ℂ) = ∑ α ∈ s, (starRingEnd ℂ) (u α) * v α := by
  rw [lp.inner_eq_tsum]
  have hcoord : ∀ α : Conf,
      (inner ℂ (((toLp u : Fock) : Conf → ℂ) α) (((toLp v : Fock) : Conf → ℂ) α) : ℂ)
        = (starRingEnd ℂ) (u α) * v α := by
    intro α
    simp [RCLike.inner_apply, mul_comm]
  rw [tsum_congr hcoord]
  refine tsum_eq_sum fun α hα => ?_
  have hu : u α = 0 := by
    by_contra hc
    exact hα (hs (Finsupp.mem_support_iff.mpr hc))
  rw [hu, map_zero, zero_mul]

theorem inner_toLp (u v : FockAlg) :
    (inner ℂ (toLp u) (toLp v) : ℂ) = ∑ α ∈ u.support, (starRingEnd ℂ) (u α) * v α :=
  inner_toLp_of_subset (Finset.Subset.refl _) v

theorem inner_creA_left (j : ℕ) (u v : FockAlg) :
    (inner ℂ (toLp (creA j u)) (toLp v) : ℂ) = inner ℂ (toLp u) (toLp (annA j v)) := by
  rw [inner_toLp_of_subset (support_creA j u) v, inner_toLp u (annA j v),
    Finset.sum_image (fun x _ y _ h => up_injective j h)]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [creA_apply, up_self, dn_up, annA_apply]
  have hcast : ((β j + 1 : ℕ) : ℝ) = ((β j : ℝ) + 1) := by push_cast; ring
  rw [hcast, map_mul, Complex.conj_ofReal]
  ring

theorem inner_creA_right (j : ℕ) (u v : FockAlg) :
    (inner ℂ (toLp u) (toLp (creA j v)) : ℂ) = inner ℂ (toLp (annA j u)) (toLp v) := by
  have h := inner_creA_left j v u
  have := congrArg (starRingEnd ℂ) h
  rwa [inner_conj_symm, inner_conj_symm] at this

@[simp] theorem coe_fockEquiv (u : FockAlg) : ((fockEquiv u : lpFiniteModes Conf) : Fock)
    = toLp u := rfl

theorem coe_fockEquiv_symm (x : lpFiniteModes Conf) :
    ((x : lpFiniteModes Conf) : Fock) = toLp (fockEquiv.symm x) := by
  rw [← coe_fockEquiv, LinearEquiv.apply_symm_apply]

theorem creVec_apply (v : ℕ →₀ ℂ) (x : FockAlg) :
    creVec v x = ∑ j ∈ v.support, v j • creA j x := by
  simp [creVec, LinearMap.sum_apply]

@[simp] theorem dGamma_single (col : ℕ → (ℕ →₀ ℂ)) (β : Conf) (c : ℂ) :
    dGamma col (Finsupp.single β c)
      = c • ∑ k ∈ β.support, creVec (col k) (annA k (Finsupp.single β 1)) := by
  simp [dGamma, LinearMap.toSpanSingleton]

theorem sum_creVec_annA_subset (col : ℕ → (ℕ →₀ ℂ)) (u : FockAlg) {K L : Finset ℕ}
    (hKL : K ⊆ L) (hK : modes u ⊆ K) :
    ∑ k ∈ K, creVec (col k) (annA k u) = ∑ k ∈ L, creVec (col k) (annA k u) :=
  Finset.sum_subset hKL fun k _ hk => by
    rw [annA_eq_zero_of_not_mem_modes (fun hc => hk (hK hc)), map_zero]

theorem dGamma_eq_sum_aux (col : ℕ → (ℕ →₀ ℂ)) (u : FockAlg) :
    ∀ K : Finset ℕ, modes u ⊆ K → dGamma col u = ∑ k ∈ K, creVec (col k) (annA k u) := by
  classical
  induction u using Finsupp.induction_linear with
  | zero => intro K _; simp
  | add f g hf hg =>
    intro K hK
    have hL1 : modes f ⊆ K ∪ (modes f ∪ modes g) := fun x hx =>
      Finset.mem_union_right _ (Finset.mem_union_left _ hx)
    have hL2 : modes g ⊆ K ∪ (modes f ∪ modes g) := fun x hx =>
      Finset.mem_union_right _ (Finset.mem_union_right _ hx)
    have hKL : K ⊆ K ∪ (modes f ∪ modes g) := Finset.subset_union_left
    rw [map_add, hf _ hL1, hg _ hL2, ← Finset.sum_add_distrib,
      sum_creVec_annA_subset col (f + g) hKL hK]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_add, map_add]
  | single β c =>
    intro K hK
    have hsingle : (Finsupp.single β c : FockAlg) = c • Finsupp.single β (1 : ℂ) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    by_cases hc : c = 0
    · subst hc
      simp
    have hb : β.support ⊆ K := by
      refine fun i hi => hK ?_
      exact Finset.mem_biUnion.mpr ⟨β, Finsupp.mem_support_iff.mpr (by simpa using hc), hi⟩
    have hzero : ∀ k ∈ K, k ∉ β.support →
        creVec (col k) (annA k (Finsupp.single β c)) = 0 := by
      intro k _ hk
      have hβ : β k = 0 := by simpa using hk
      have hz : annA k (Finsupp.single β c) = 0 := by
        rw [annA_single, hβ]
        simp
      rw [hz, map_zero]
    rw [← Finset.sum_subset hb hzero, dGamma_single, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hsingle, map_smul, map_smul]

theorem dGamma_eq_sum (col : ℕ → (ℕ →₀ ℂ)) {u : FockAlg} {K : Finset ℕ} (hK : modes u ⊆ K) :
    dGamma col u = ∑ k ∈ K, creVec (col k) (annA k u) :=
  dGamma_eq_sum_aux col u K hK

theorem dGamma_one_particle (col : ℕ → (ℕ →₀ ℂ)) (k : ℕ) :
    dGamma col (Finsupp.single (Finsupp.single k 1) 1)
      = ∑ j ∈ (col k).support, (col k) j • Finsupp.single (Finsupp.single j 1) (1 : ℂ) := by
  classical
  have hup : ∀ j : ℕ, up j (0 : Conf) = Finsupp.single j 1 := by
    intro j
    refine Finsupp.ext fun i => ?_
    by_cases h : i = j
    · subst h; simp
    · rw [up_of_ne _ h]
      simp [h]
  have hsupp : (Finsupp.single k 1 : Conf).support = {k} :=
    Finsupp.support_single_ne_zero k one_ne_zero
  have hdn : dn k (Finsupp.single k 1 : Conf) = 0 := by
    refine Finsupp.ext fun i => ?_
    by_cases h : i = k
    · subst h; simp
    · rw [dn_of_ne _ h]
      simp [h]
  rw [dGamma_single, hsupp]
  have hann : annA k (Finsupp.single (Finsupp.single k 1 : Conf) (1 : ℂ))
      = Finsupp.single (0 : Conf) (1 : ℂ) := by
    rw [annA_single, hdn]
    simp
  rw [Finset.sum_singleton, hann, one_smul, creVec_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [creA_single, hup j]
  simp

@[simp] theorem toLp_zero : toLp (0 : FockAlg) = 0 := map_zero toLpL

theorem inner_creVec_annA (col : ℕ → (ℕ →₀ ℂ)) (u v : FockAlg) (k : ℕ) {L : Finset ℕ}
    (h : (col k).support ⊆ L) :
    (inner ℂ (toLp (creVec (col k) (annA k u))) (toLp v) : ℂ)
      = ∑ j ∈ L, (starRingEnd ℂ) ((col k) j)
          * inner ℂ (toLp (annA k u)) (toLp (annA j v)) := by
  have hexp : toLp (creVec (col k) (annA k u))
      = ∑ j ∈ (col k).support, (col k) j • toLp (creA j (annA k u)) := by
    rw [creVec_apply, ← toLpL_apply, map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, toLpL_apply]
  rw [hexp, sum_inner, ← Finset.sum_subset h (fun j _ hj => by
    rw [Finsupp.notMem_support_iff.mp hj, map_zero, zero_mul])]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_left, inner_creA_left]

theorem inner_annA_creVec (col : ℕ → (ℕ →₀ ℂ)) (u v : FockAlg) (j : ℕ) {L : Finset ℕ}
    (h : (col j).support ⊆ L) :
    (inner ℂ (toLp u) (toLp (creVec (col j) (annA j v))) : ℂ)
      = ∑ k ∈ L, (col j) k * inner ℂ (toLp (annA k u)) (toLp (annA j v)) := by
  have hexp : toLp (creVec (col j) (annA j v))
      = ∑ k ∈ (col j).support, (col j) k • toLp (creA k (annA j v)) := by
    rw [creVec_apply, ← toLpL_apply, map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [map_smul, toLpL_apply]
  rw [hexp, inner_sum, ← Finset.sum_subset h (fun k _ hk => by
    rw [Finsupp.notMem_support_iff.mp hk, zero_mul])]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inner_smul_right, inner_creA_right]

theorem inner_dGamma_left (col : ℕ → (ℕ →₀ ℂ)) (u v : FockAlg) {L : Finset ℕ}
    (hu : modes u ⊆ L)
    (hL : ∀ k ∈ modes u ∪ modes v, (col k).support ⊆ L) :
    (inner ℂ (toLp (dGamma col u)) (toLp v) : ℂ)
      = ∑ k ∈ L, ∑ j ∈ L,
        (starRingEnd ℂ) ((col k) j) * inner ℂ (toLp (annA k u)) (toLp (annA j v)) := by
  have hsum : toLp (dGamma col u) = ∑ k ∈ L, toLp (creVec (col k) (annA k u)) := by
    rw [dGamma_eq_sum col hu, ← toLpL_apply, map_sum]
    rfl
  rw [hsum, sum_inner]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hku : k ∈ modes u
  · exact inner_creVec_annA col u v k (hL k (Finset.mem_union_left _ hku))
  · have h0 : annA k u = 0 := annA_eq_zero_of_not_mem_modes hku
    rw [h0, map_zero]
    simp

theorem inner_dGamma_right (col : ℕ → (ℕ →₀ ℂ)) (u v : FockAlg) {L : Finset ℕ}
    (hv : modes v ⊆ L)
    (hL : ∀ k ∈ modes u ∪ modes v, (col k).support ⊆ L) :
    (inner ℂ (toLp u) (toLp (dGamma col v)) : ℂ)
      = ∑ j ∈ L, ∑ k ∈ L,
        (col j) k * inner ℂ (toLp (annA k u)) (toLp (annA j v)) := by
  have hsum : toLp (dGamma col v) = ∑ j ∈ L, toLp (creVec (col j) (annA j v)) := by
    rw [dGamma_eq_sum col hv, ← toLpL_apply, map_sum]
    rfl
  rw [hsum, inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hjv : j ∈ modes v
  · exact inner_annA_creVec col u v j (hL j (Finset.mem_union_right _ hjv))
  · have h0 : annA j v = 0 := annA_eq_zero_of_not_mem_modes hjv
    rw [h0, map_zero]
    simp

theorem modes_left_subset_closure (col : ℕ → (ℕ →₀ ℂ)) (u v : FockAlg) :
    modes u ⊆ closureModes col u v := fun _ hx =>
  Finset.mem_union_left _ (Finset.mem_union_left _ hx)

theorem modes_right_subset_closure (col : ℕ → (ℕ →₀ ℂ)) (u v : FockAlg) :
    modes v ⊆ closureModes col u v := fun _ hx =>
  Finset.mem_union_left _ (Finset.mem_union_right _ hx)

theorem col_support_subset_closure (col : ℕ → (ℕ →₀ ℂ)) (u v : FockAlg) :
    ∀ k ∈ modes u ∪ modes v, (col k).support ⊆ closureModes col u v := by
  intro k hk i hi
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨k, hk, hi⟩)

theorem inner_dGamma_symm {col : ℕ → (ℕ →₀ ℂ)} (hherm : IsHermCol col) (u v : FockAlg) :
    (inner ℂ (toLp (dGamma col u)) (toLp v) : ℂ) = inner ℂ (toLp u) (toLp (dGamma col v)) := by
  rw [inner_dGamma_left col u v (modes_left_subset_closure col u v)
      (col_support_subset_closure col u v),
    inner_dGamma_right col u v (modes_right_subset_closure col u v)
      (col_support_subset_closure col u v),
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hherm j k, Complex.conj_conj]

theorem inner_dGamma_nonneg {col : ℕ → (ℕ →₀ ℂ)} (hpos : IsPosCol col) (u : FockAlg) :
    0 ≤ (inner ℂ (toLp u) (toLp (dGamma col u)) : ℂ).re := by
  classical
  set L := closureModes col u u with hLdef
  set S : Finset Conf := L.biUnion fun k => (annA k u).support with hSdef
  rw [inner_dGamma_right col u u (modes_right_subset_closure col u u)
    (col_support_subset_closure col u u)]
  have hinner : ∀ k ∈ L, ∀ j : ℕ,
      (inner ℂ (toLp (annA k u)) (toLp (annA j u)) : ℂ)
        = ∑ α ∈ S, (starRingEnd ℂ) ((annA k u) α) * (annA j u) α := by
    intro k hk j
    exact inner_toLp_of_subset (fun α hα => Finset.mem_biUnion.mpr ⟨k, hk, hα⟩) _
  have hstep : (∑ j ∈ L, ∑ k ∈ L, (col j) k * inner ℂ (toLp (annA k u)) (toLp (annA j u)))
      = ∑ α ∈ S, ∑ j ∈ L, ∑ k ∈ L,
          (starRingEnd ℂ) ((annA j u) α) * (col k) j * ((annA k u) α) := by
    have h1 : (∑ j ∈ L, ∑ k ∈ L, (col j) k * inner ℂ (toLp (annA k u)) (toLp (annA j u)))
        = ∑ j ∈ L, ∑ k ∈ L, ∑ α ∈ S,
            (col j) k * ((starRingEnd ℂ) ((annA k u) α) * (annA j u) α) := by
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k hk => ?_
      rw [hinner k hk j, Finset.mul_sum]
    rw [h1]
    rw [Finset.sum_comm (s := L) (t := L)]
    rw [show (∑ k ∈ L, ∑ j ∈ L, ∑ α ∈ S,
          (col j) k * ((starRingEnd ℂ) ((annA k u) α) * (annA j u) α))
        = ∑ k ∈ L, ∑ α ∈ S, ∑ j ∈ L,
          (col j) k * ((starRingEnd ℂ) ((annA k u) α) * (annA j u) α) from
      Finset.sum_congr rfl fun k _ => Finset.sum_comm]
    rw [Finset.sum_comm (s := L) (t := S)]
    refine Finset.sum_congr rfl fun α _ => ?_
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hstep, Complex.re_sum]
  refine Finset.sum_nonneg fun α _ => hpos L fun k => (annA k u) α

theorem coe_dGammaOp (col : ℕ → (ℕ →₀ ℂ)) (x : lpFiniteModes Conf) :
    dGammaOp col x = toLp (dGamma col (fockEquiv.symm x)) := by
  simp [dGammaOp, LinearEquiv.conj_apply, coe_fockEquiv]

theorem dGammaOp_symmetricOn {col : ℕ → (ℕ →₀ ℂ)} (hherm : IsHermCol col) :
    SymmetricOn (lpFiniteModes Conf) (dGammaOp col) := by
  intro x y
  rw [coe_dGammaOp, coe_dGammaOp, coe_fockEquiv_symm x, coe_fockEquiv_symm y]
  exact inner_dGamma_symm hherm _ _

theorem dGammaOp_quadForm_nonneg {col : ℕ → (ℕ →₀ ℂ)} (hpos : IsPosCol col)
    (x : lpFiniteModes Conf) : 0 ≤ quadForm (dGammaOp col) x := by
  rw [quadForm, coe_dGammaOp, coe_fockEquiv_symm x]
  exact inner_dGamma_nonneg hpos _

theorem finiteOccupation_dense : Dense ((lpFiniteModes Conf : Submodule ℂ Fock) : Set Fock) :=
  lpFiniteModes_dense

theorem dGammaOpB_symmetricOn {ε : ℕ ≃ Conf} {col : ℕ → (ℕ →₀ ℂ)} (hherm : IsHermCol col) :
    SymmetricOn (finiteModeDomain (fockBasisN ε)) (dGammaOpB ε col) := by
  intro x y
  exact dGammaOp_symmetricOn hherm
    (LinearEquiv.ofEq _ _ (finiteModeDomain_fockBasisN ε) x)
    (LinearEquiv.ofEq _ _ (finiteModeDomain_fockBasisN ε) y)

theorem dGammaOpB_quadForm_nonneg {ε : ℕ ≃ Conf} {col : ℕ → (ℕ →₀ ℂ)} (hpos : IsPosCol col)
    (x : finiteModeDomain (fockBasisN ε)) : 0 ≤ quadForm (dGammaOpB ε col) x :=
  dGammaOp_quadForm_nonneg hpos
    (LinearEquiv.ofEq _ _ (finiteModeDomain_fockBasisN ε) x)
end
end BookProof.FockSecondQuantization

namespace BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert
open BookProof.YangMillsHermite BookProof.HermiteProductCore
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
theorem dGamma_friedrichs_extension {col : ℕ → (ℕ →₀ ℂ)} (hherm : IsHermCol col)
    (hpos : IsPosCol col) :
    ∃ (Dom : Submodule ℂ Fock) (A : Dom →ₗ[ℂ] Fock),
      IsPositiveSelfAdjointExtension (dGammaOp col) A :=
  SirkFriedrichsAux.friedrichs_extension_exists
    ⟨lpFiniteModes Conf, dGammaOp col, dGammaOp_symmetricOn hherm,
      dGammaOp_quadForm_nonneg hpos⟩
    finiteOccupation_dense

theorem coordFinsupp_apply {b : HilbertBasis ℕ ℂ F} {x : F} (hx : x ∈ finiteModeDomain b)
    (j : ℕ) : coordFinsupp b x j = inner ℂ (b j) x := by
  classical
  have hx' : x ∈ Submodule.span ℂ (Set.range b) := hx
  have hspec : ((Finsupp.mem_span_range_iff_exists_finsupp.mp hx').choose.sum
      fun i a => a • b i) = x := (Finsupp.mem_span_range_iff_exists_finsupp.mp hx').choose_spec
  rw [coordFinsupp, dif_pos hx]
  conv_rhs => rw [← hspec]
  rw [← Finsupp.linearCombination_apply, b.orthonormal.inner_right_finsupp]

theorem opCol_apply (b : HilbertBasis ℕ ℂ F) (A : finiteModeDomain b →ₗ[ℂ] finiteModeDomain b)
    (k j : ℕ) :
    opCol b A k j
      = inner ℂ (b j) ((A ⟨b k, Submodule.subset_span ⟨k, rfl⟩⟩ : finiteModeDomain b) : F) :=
  coordFinsupp_apply (A ⟨b k, Submodule.subset_span ⟨k, rfl⟩⟩ : finiteModeDomain b).2 j

theorem isHermCol_opCol {b : HilbertBasis ℕ ℂ F}
    {A : finiteModeDomain b →ₗ[ℂ] finiteModeDomain b}
    (hA : SymmetricOn (finiteModeDomain b) ((finiteModeDomain b).subtype.comp A)) :
    IsHermCol (opCol b A) := by
  intro j k
  have h := hA ⟨b k, Submodule.subset_span ⟨k, rfl⟩⟩ ⟨b j, Submodule.subset_span ⟨j, rfl⟩⟩
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.subtype_apply] at h
  rw [opCol_apply, opCol_apply, ← h, inner_conj_symm]

theorem isPosCol_opCol {b : HilbertBasis ℕ ℂ F}
    {A : finiteModeDomain b →ₗ[ℂ] finiteModeDomain b}
    (hpos : ∀ x, 0 ≤ quadForm ((finiteModeDomain b).subtype.comp A) x) :
    IsPosCol (opCol b A) := by
  intro S c
  classical
  set x : finiteModeDomain b :=
    ∑ k ∈ S, c k • (⟨b k, Submodule.subset_span ⟨k, rfl⟩⟩ : finiteModeDomain b) with hxdef
  have hxc : ((x : finiteModeDomain b) : F) = ∑ k ∈ S, c k • b k := by
    rw [hxdef, Submodule.coe_sum]
    exact Finset.sum_congr rfl fun k _ => rfl
  have hAx : ((A x : finiteModeDomain b) : F)
      = ∑ k ∈ S, c k • ((A ⟨b k, Submodule.subset_span ⟨k, rfl⟩⟩ : finiteModeDomain b) : F) := by
    rw [hxdef, map_sum, Submodule.coe_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [map_smul]; rfl
  have hval : (inner ℂ ((x : finiteModeDomain b) : F)
        (((finiteModeDomain b).subtype.comp A) x) : ℂ)
      = ∑ j ∈ S, ∑ k ∈ S, (starRingEnd ℂ) (c j) * opCol b A k j * c k := by
    change (inner ℂ ((x : finiteModeDomain b) : F)
      ((A x : finiteModeDomain b) : F) : ℂ) = _
    rw [hxc, hAx, sum_inner]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_smul_left, inner_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [inner_smul_right, opCol_apply]
    ring
  have hq := hpos x
  rw [quadForm, hval] at hq
  exact hq

theorem secondQuantization_friedrichs (b : HilbertBasis ℕ ℂ F)
    (A : finiteModeDomain b →ₗ[ℂ] finiteModeDomain b)
    (hA : SymmetricOn (finiteModeDomain b) ((finiteModeDomain b).subtype.comp A))
    (hpos : ∀ x, 0 ≤ quadForm ((finiteModeDomain b).subtype.comp A) x) :
    ∃ (Dom : Submodule ℂ Fock) (A' : Dom →ₗ[ℂ] Fock),
      IsPositiveSelfAdjointExtension (dGammaOp (opCol b A)) A' :=
  dGamma_friedrichs_extension (isHermCol_opCol hA) (isPosCol_opCol hpos)

theorem coe_ymOnePart (e : ℕ ≃ (Fin 99 →₀ ℕ)) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ)
    (x : finiteModeDomain (coreBasis e)) :
    ((ymOnePart e fabc x : finiteModeDomain (coreBasis e)) : L2d 99)
      = ymHamiltonian (coreRepBasis e) fabc x := rfl

theorem ymFockCol_apply (e : ℕ ≃ (Fin 99 →₀ ℕ)) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (k j : ℕ) :
    ymFockCol e fabc k j
      = inner ℂ (coreBasis e j)
          (ymHamiltonian (coreRepBasis e) fabc
            ⟨coreBasis e k, Submodule.subset_span ⟨k, rfl⟩⟩) :=
  opCol_apply _ _ k j

theorem ym_fock_friedrichs_extension (e : ℕ ≃ (Fin 99 →₀ ℕ))
    (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) :
    ∃ (Dom : Submodule ℂ Fock) (A : Dom →ₗ[ℂ] Fock),
      IsPositiveSelfAdjointExtension (dGammaOp (ymFockCol e fabc)) A :=
  secondQuantization_friedrichs (coreBasis e) (ymOnePart e fabc)
    (ymHamiltonian_symmetricOn (coreRepBasis e) fabc)
    (ymHamiltonian_quadForm_nonneg (coreRepBasis e) fabc)
end BookProof.FockSecondQuantization

open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsHermite
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert
open BookProof.HermiteProductCore
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
theorem solution (b : HilbertBasis ℕ ℂ F)
    (A : finiteModeDomain b →ₗ[ℂ] finiteModeDomain b)
    (hA : SymmetricOn (finiteModeDomain b) ((finiteModeDomain b).subtype.comp A))
    (hpos : ∀ x, 0 ≤ quadForm ((finiteModeDomain b).subtype.comp A) x) :
    ∃ (Dom : Submodule ℂ Fock) (A' : Dom →ₗ[ℂ] Fock),
      IsPositiveSelfAdjointExtension (dGammaOp (opCol b A)) A' := by
  exact BookProof.FockSecondQuantization.secondQuantization_friedrichs b A hA hpos
#print axioms solution
