-- Prove2me | solution 1 for BookProof.QgHermiteFriedrichs.hermiteCore_friedrichs_extension
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T16:45:55.171025+00:00
-- url     : https://prove2.me/submissions/3500aea6-4bb9-4274-bf4b-50c2dfa63c61

/- Adapted from Leonardo Pedro, timepiece commit 61595bc, Apache-2.0.
https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteFriedrichs.lean
Supporting complete proofs: ChapterFriedrichsExtension.lean, ChapterHashimotoShiftInvert.lean,
ChapterQgHermiteCore.lean, and ChapterStarobinskyPotential.lean, same revision. -/
import Mathlib
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterYangMillsHermite
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

open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs BookProof.FarisLavine
open BookProof.Starobinsky
noncomputable section
namespace BookProof.QgHermiteFriedrichs
variable {d : ℕ}

@[simp] theorem cpoly_add (p q : MvPolynomial (Fin d) ℂ) :
    cpoly (p + q) = cpoly p + cpoly q := by
  simp [cpoly]

@[simp] theorem cpoly_mul (p q : MvPolynomial (Fin d) ℂ) :
    cpoly (p * q) = cpoly p * cpoly q := by
  simp [cpoly]

@[simp] theorem cpoly_X (j : Fin d) : cpoly (X j : MvPolynomial (Fin d) ℂ) = X j := by
  simp [cpoly]

@[simp] theorem cpoly_C (a : ℂ) :
    cpoly (C a : MvPolynomial (Fin d) ℂ) = C (starRingEnd ℂ a) := by
  simp [cpoly]

theorem cpoly_pderiv (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    cpoly (pderiv j p) = pderiv j (cpoly p) := pderiv_map.symm

theorem conj_polyEval (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    (starRingEnd ℂ) (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p)
      = MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (cpoly p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [cpoly]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp only [cpoly] at hp ⊢; simp [hp]

theorem conj_pgFun (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    (starRingEnd ℂ) (pgFun p x) = pgFun (cpoly p) x := by
  simp only [pgFun, map_mul, Complex.conj_ofReal, conj_polyEval]

@[simp] theorem cpoly_sub (p q : MvPolynomial (Fin d) ℂ) :
    cpoly (p - q) = cpoly p - cpoly q := by
  simp [cpoly]

@[simp] theorem cpoly_neg (p : MvPolynomial (Fin d) ℂ) : cpoly (-p) = -cpoly p := by
  simp [cpoly]

theorem cpoly_sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin d) ℂ) :
    cpoly (∑ i ∈ s, f i) = ∑ i ∈ s, cpoly (f i) :=
  map_sum (MvPolynomial.map (starRingEnd ℂ)) f s

theorem cpoly_coreD (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    cpoly (coreD j p) = coreD j (cpoly p) := by
  have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by norm_num [Complex.ext_iff]
  unfold coreD
  rw [cpoly_sub, cpoly_pderiv, cpoly_mul, cpoly_mul, cpoly_X, cpoly_C, hhalf]

theorem inner_pgLp_pgLp (p q : MvPolynomial (Fin d) ℂ) :
    (inner ℂ (pgLp p) (pgLp q) : ℂ) = gaussInt (cpoly p * q) := by
  rw [inner_pgLp, gaussInt]
  refine integral_congr_ae ?_
  filter_upwards [pgLp_coeFn q] with x hx
  rw [hx, conj_pgFun]
  simp only [pgFun, map_mul, gaussWD_eq_sq]
  push_cast
  ring

theorem gaussInt_sub (r s : MvPolynomial (Fin d) ℂ) :
    gaussInt (r - s) = gaussInt r - gaussInt s := by
  have h : r - s = r + (-1 : ℂ) • s := by module
  rw [h, gaussInt_add, gaussInt_smul]
  ring

theorem gaussInt_neg (r : MvPolynomial (Fin d) ℂ) : gaussInt (-r) = -gaussInt r := by
  have h : -r = (-1 : ℂ) • r := by module
  rw [h, gaussInt_smul]
  ring

theorem gaussInt_coreD_raw (j : Fin d) (a b : MvPolynomial (Fin d) ℂ) :
    gaussInt (coreD j a * b) = -gaussInt (a * coreD j b) := by
  have hC2 : (C (1 / 2 : ℂ) : MvPolynomial (Fin d) ℂ) * 2 = 1 := by
    have h2 : ((2 : MvPolynomial (Fin d) ℂ)) = C (2 : ℂ) :=
      (MvPolynomial.ext _ _ (congrFun rfl)).symm
    rw [h2, ← C_mul]
    norm_num
  have hsum : coreD j a * b + a * coreD j b = pderiv j (a * b) - X j * (a * b) := by
    simp only [coreD, pderiv_mul, sub_mul, mul_sub]
    linear_combination (-(X j * a * b)) * hC2
  have h0 : gaussInt (coreD j a * b + a * coreD j b) = 0 := by
    rw [hsum, gaussInt_sub, gaussInt_pderiv, sub_self]
  rw [gaussInt_add] at h0
  linear_combination h0

theorem gaussInt_coreD (j : Fin d) (p q : MvPolynomial (Fin d) ℂ) :
    gaussInt (cpoly (coreD j p) * q) = -gaussInt (cpoly p * coreD j q) := by
  rw [cpoly_coreD, gaussInt_coreD_raw]

theorem cpoly_kinPoly (p : MvPolynomial (Fin d) ℂ) :
    cpoly (kinPoly p) = kinPoly (cpoly p) := by
  simp only [kinPoly, cpoly_neg, cpoly_sum, cpoly_coreD]

theorem gaussInt_kinPoly (p q : MvPolynomial (Fin d) ℂ) :
    gaussInt (cpoly p * kinPoly q) = ∑ j : Fin d, gaussInt (cpoly (coreD j p) * coreD j q) := by
  have hmul : cpoly p * kinPoly q = -∑ j : Fin d, cpoly p * coreD j (coreD j q) := by
    simp only [kinPoly, Finset.mul_sum, mul_neg]
  rw [hmul, gaussInt_neg, gaussInt_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [gaussInt_coreD j p (coreD j q)]

theorem gaussInt_kinPoly_left (p q : MvPolynomial (Fin d) ℂ) :
    gaussInt (cpoly (kinPoly p) * q) = ∑ j : Fin d, gaussInt (cpoly (coreD j p) * coreD j q) := by
  have hmul : cpoly (kinPoly p) * q = -∑ j : Fin d, coreD j (coreD j (cpoly p)) * q := by
    rw [cpoly_kinPoly]
    simp only [kinPoly, Finset.sum_mul, neg_mul]
  rw [hmul, gaussInt_neg, gaussInt_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [gaussInt_coreD_raw j (coreD j (cpoly p)) q, cpoly_coreD, neg_neg]

variable (W : Vd d → ℝ)

theorem potLp_coeFn (hWc : Continuous W) (hWb : ExpBounded W) (p : MvPolynomial (Fin d) ℂ) :
    (potLp W hWc hWb p : Vd d → ℂ) =ᵐ[volume] fun x => ((W x : ℝ) : ℂ) * pgFun p x :=
  (memLp_mul_pgFun_of_expBounded hWc hWb p).coeFn_toLp

theorem coreEquiv_apply (p : MvPolynomial (Fin d) ℂ) :
    ((coreEquiv p : polyGaussCore (d := d)) : L2d d) = pgLp p := rfl

theorem coreEquiv_symm_pgLp (p : MvPolynomial (Fin d) ℂ) :
    coreEquiv.symm ⟨pgLp p, pgLp_mem_core p⟩ = p := by
  apply coreEquiv.injective
  rw [LinearEquiv.apply_symm_apply]
  exact Subtype.ext rfl

theorem hamCore_pgLp (hWc : Continuous W) (hWb : ExpBounded W) (p : MvPolynomial (Fin d) ℂ) :
    hamCore W hWc hWb ⟨pgLp p, pgLp_mem_core p⟩ = hamPoly W hWc hWb p := by
  simp only [hamCore, LinearMap.comp_apply, LinearEquiv.coe_coe, coreEquiv_symm_pgLp]
  rfl

theorem conj_mul_self (z : ℂ) : (starRingEnd ℂ) z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [mul_comm, Complex.mul_conj]
  norm_cast
  exact Complex.normSq_eq_norm_sq z

theorem inner_L2_eq (f g : L2d d) :
    (inner ℂ f g : ℂ)
      = ∫ x : Vd d, (starRingEnd ℂ) ((f : Vd d → ℂ) x) * (g : Vd d → ℂ) x := by
  rw [L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [RCLike.inner_apply]
  ring

theorem inner_pgLp_potLp (hWc : Continuous W) (hWb : ExpBounded W)
    (p q : MvPolynomial (Fin d) ℂ) :
    (inner ℂ (pgLp p) (potLp W hWc hWb q) : ℂ)
      = ∫ x : Vd d, (starRingEnd ℂ) (pgFun p x) * (((W x : ℝ) : ℂ) * pgFun q x) := by
  rw [inner_pgLp]
  refine integral_congr_ae ?_
  filter_upwards [potLp_coeFn W hWc hWb q] with x hx
  rw [hx]

theorem inner_potLp_pgLp (hWc : Continuous W) (hWb : ExpBounded W)
    (p q : MvPolynomial (Fin d) ℂ) :
    (inner ℂ (potLp W hWc hWb p) (pgLp q) : ℂ)
      = ∫ x : Vd d, (starRingEnd ℂ) (((W x : ℝ) : ℂ) * pgFun p x) * pgFun q x := by
  rw [inner_L2_eq]
  refine integral_congr_ae ?_
  filter_upwards [potLp_coeFn W hWc hWb p, pgLp_coeFn q] with x hx hy
  rw [hx, hy]

theorem inner_potLp_symm (hWc : Continuous W) (hWb : ExpBounded W)
    (p q : MvPolynomial (Fin d) ℂ) :
    (inner ℂ (potLp W hWc hWb p) (pgLp q) : ℂ) = inner ℂ (pgLp p) (potLp W hWc hWb q) := by
  rw [inner_potLp_pgLp, inner_pgLp_potLp]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [map_mul, Complex.conj_ofReal]
  ring

theorem hamCore_symmetricOn (hWc : Continuous W) (hWb : ExpBounded W) :
    SymmetricOn (polyGaussCore (d := d)) (hamCore W hWc hWb) := by
  intro x y
  obtain ⟨p, hp⟩ := x.2
  obtain ⟨q, hq⟩ := y.2
  have hx : x = ⟨pgLp p, pgLp_mem_core p⟩ := Subtype.ext hp.symm
  have hy : y = ⟨pgLp q, pgLp_mem_core q⟩ := Subtype.ext hq.symm
  rw [hx, hy, hamCore_pgLp, hamCore_pgLp]
  change (inner ℂ (hamPoly W hWc hWb p) (pgLp q) : ℂ) = inner ℂ (pgLp p) (hamPoly W hWc hWb q)
  simp only [hamPoly, inner_add_left, inner_add_right]
  congr 1
  · rw [inner_pgLp_pgLp, inner_pgLp_pgLp, gaussInt_kinPoly_left, gaussInt_kinPoly]
  · exact inner_potLp_symm W hWc hWb p q

theorem re_gaussInt_kinPoly_self (p : MvPolynomial (Fin d) ℂ) :
    (gaussInt (cpoly p * kinPoly p)).re = ∑ j : Fin d, ‖pgLp (coreD j p)‖ ^ 2 := by
  rw [gaussInt_kinPoly]
  have h : ∀ j : Fin d, gaussInt (cpoly (coreD j p) * coreD j p)
      = ((‖pgLp (coreD j p)‖ ^ 2 : ℝ) : ℂ) := by
    intro j
    rw [← inner_pgLp_pgLp, inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
    norm_cast
  simp only [h, ← Complex.ofReal_sum, Complex.ofReal_re]

theorem norm_sq_pgLp (p : MvPolynomial (Fin d) ℂ) :
    ‖pgLp p‖ ^ 2 = ∫ x : Vd d, ‖pgFun p x‖ ^ 2 := by
  have h1 : (inner ℂ (pgLp p) (pgLp p) : ℂ) = ((∫ x : Vd d, ‖pgFun p x‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_L2_eq, ← integral_complex_ofReal]
    refine integral_congr_ae ?_
    filter_upwards [pgLp_coeFn p] with x hx
    rw [hx, conj_mul_self]
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)] at h1
  refine Complex.ofReal_inj.mp ?_
  push_cast
  exact h1

theorem integrable_potential_normSq (hWc : Continuous W) (hWb : ExpBounded W)
    (p : MvPolynomial (Fin d) ℂ) :
    Integrable (fun x : Vd d => W x * ‖pgFun p x‖ ^ 2) (volume : Measure (Vd d)) := by
  have hu : MemLp (fun x : Vd d => ‖pgFun p x‖) 2 (volume : Measure (Vd d)) :=
    (memLp_pgFun p).norm
  have hv : MemLp (fun x : Vd d => W x * ‖pgFun p x‖) 2 (volume : Measure (Vd d)) := by
    refine (memLp_mul_pgFun_of_expBounded hWc hWb p).of_le
      ((hWc.mul ((continuous_pgFun p).norm)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg (pgFun p x))]
  have hmul := hv.integrable_mul hu
  refine hmul.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Pi.mul_apply]
  ring

theorem hamCore_quadForm_ge (hWc : Continuous W) (hWb : ExpBounded W) (c : ℝ)
    (hlb : ∀ x, -c ≤ W x) (x : (polyGaussCore (d := d))) :
    -c * ‖(x : L2d d)‖ ^ 2 ≤ quadForm (hamCore W hWc hWb) x := by
  obtain ⟨p, hp⟩ := x.2
  have hx : x = ⟨pgLp p, pgLp_mem_core p⟩ := Subtype.ext hp.symm
  subst hx
  -- the potential part, as a real integral
  have hpot : (inner ℂ (pgLp p) (potLp W hWc hWb p) : ℂ)
      = ((∫ y : Vd d, W y * ‖pgFun p y‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_pgLp_potLp, ← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have hy : (starRingEnd ℂ) (pgFun p y) * (((W y : ℝ) : ℂ) * pgFun p y)
        = ((W y : ℝ) : ℂ) * ((starRingEnd ℂ) (pgFun p y) * pgFun p y) := by ring
    change (starRingEnd ℂ) (pgFun p y) * (((W y : ℝ) : ℂ) * pgFun p y)
        = ((W y * ‖pgFun p y‖ ^ 2 : ℝ) : ℂ)
    rw [hy, conj_mul_self]
    push_cast
    ring
  have hint : Integrable (fun y : Vd d => W y * ‖pgFun p y‖ ^ 2) (volume : Measure (Vd d)) :=
    integrable_potential_normSq W hWc hWb p
  have hint2 : Integrable (fun y : Vd d => -c * ‖pgFun p y‖ ^ 2) (volume : Measure (Vd d)) := by
    have h1 : MemLp (fun y : Vd d => ‖pgFun p y‖) 2 (volume : Measure (Vd d)) :=
      (memLp_pgFun p).norm
    have h2 := h1.integrable_mul h1
    refine (h2.const_mul (-c)).congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.mul_apply]
    ring
  have hmono : ∫ y : Vd d, -c * ‖pgFun p y‖ ^ 2 ≤ ∫ y : Vd d, W y * ‖pgFun p y‖ ^ 2 := by
    refine integral_mono hint2 hint fun y => ?_
    have := hlb y
    nlinarith [sq_nonneg ‖pgFun p y‖]
  have hconst : ∫ y : Vd d, -c * ‖pgFun p y‖ ^ 2 = -c * ‖pgLp p‖ ^ 2 := by
    rw [integral_const_mul, ← norm_sq_pgLp]
  -- assemble
  have hquad : quadForm (hamCore W hWc hWb) ⟨pgLp p, pgLp_mem_core p⟩
      = (∑ j : Fin d, ‖pgLp (coreD j p)‖ ^ 2) + ∫ y : Vd d, W y * ‖pgFun p y‖ ^ 2 := by
    simp only [quadForm, hamCore_pgLp, hamPoly, inner_add_right, Complex.add_re]
    rw [inner_pgLp_pgLp, re_gaussInt_kinPoly_self, hpot, Complex.ofReal_re]
  rw [hquad]
  have hkin : 0 ≤ ∑ j : Fin d, ‖pgLp (coreD j p)‖ ^ 2 :=
    Finset.sum_nonneg fun j _ => by positivity
  have hnorm : ‖((⟨pgLp p, pgLp_mem_core p⟩ : (polyGaussCore (d := d))) : L2d d)‖ = ‖pgLp p‖ := rfl
  rw [hnorm]
  linarith [hconst ▸ hmono]

theorem hamCore_quadForm_nonneg (hWc : Continuous W) (hWb : ExpBounded W)
    (hW0 : ∀ x, 0 ≤ W x) (x : (polyGaussCore (d := d))) :
    0 ≤ quadForm (hamCore W hWc hWb) x := by
  have h := hamCore_quadForm_ge W hWc hWb 0 (by simpa using hW0) x
  simpa using h
end BookProof.QgHermiteFriedrichs
namespace BookProof.Starobinsky
theorem starobinskyV_nonneg {M alpha : ℝ} (halpha : 0 < alpha) (phi : ℝ) :
    0 ≤ starobinskyV M alpha phi := by
  have h16 : (0 : ℝ) < 16 * alpha := by linarith
  have h1 : 0 ≤ M ^ 4 / (16 * alpha) := div_nonneg (by positivity) h16.le
  exact mul_nonneg h1 (sq_nonneg _)
end BookProof.Starobinsky

namespace BookProof.QgHermiteCore
open MeasureTheory Polynomial Filter Topology
open BookProof.HermiteCore BookProof.Starobinsky BookProof.HermiteProductCore
variable {E : Type*} [NormedAddCommGroup E]
variable {d : ℕ}
theorem ExpBounded.nonneg_const {f : E → ℝ} {C c : ℝ}
    (h : ∀ x, |f x| ≤ C * Real.exp (c * ‖x‖)) : 0 ≤ C := by
  have h0 := h 0
  rw [norm_zero, mul_zero, Real.exp_zero, mul_one] at h0
  exact (abs_nonneg _).trans h0

theorem ExpBounded.add {f g : E → ℝ} (hf : ExpBounded f) (hg : ExpBounded g) :
    ExpBounded (fun x => f x + g x) := by
  obtain ⟨C1, c1, hc1, h1⟩ := hf
  obtain ⟨C2, c2, _, h2⟩ := hg
  have hC1 : 0 ≤ C1 := ExpBounded.nonneg_const h1
  have hC2 : 0 ≤ C2 := ExpBounded.nonneg_const h2
  refine ⟨C1 + C2, max c1 c2, le_trans hc1 (le_max_left _ _), fun x => ?_⟩
  have e1 : C1 * Real.exp (c1 * ‖x‖) ≤ C1 * Real.exp (max c1 c2 * ‖x‖) := by
    gcongr
    · exact le_max_left _ _
  have e2 : C2 * Real.exp (c2 * ‖x‖) ≤ C2 * Real.exp (max c1 c2 * ‖x‖) := by
    gcongr
    · exact le_max_right _ _
  calc |f x + g x| ≤ |f x| + |g x| := abs_add_le _ _
    _ ≤ C1 * Real.exp (c1 * ‖x‖) + C2 * Real.exp (c2 * ‖x‖) := add_le_add (h1 x) (h2 x)
    _ ≤ (C1 + C2) * Real.exp (max c1 c2 * ‖x‖) := by linarith

theorem ExpBounded.const_mul {f : E → ℝ} (hf : ExpBounded f) (a : ℝ) :
    ExpBounded (fun x => a * f x) := by
  obtain ⟨C, c, hc, h⟩ := hf
  refine ⟨|a| * C, c, hc, fun x => ?_⟩
  rw [abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h x) (abs_nonneg a)

theorem ExpBounded.mul {f g : E → ℝ} (hf : ExpBounded f) (hg : ExpBounded g) :
    ExpBounded (fun x => f x * g x) := by
  obtain ⟨C1, c1, hc1, h1⟩ := hf
  obtain ⟨C2, c2, hc2, h2⟩ := hg
  have hC1 : 0 ≤ C1 := ExpBounded.nonneg_const h1
  refine ⟨C1 * C2, c1 + c2, by linarith, fun x => ?_⟩
  have hexp : Real.exp (c1 * ‖x‖) * Real.exp (c2 * ‖x‖) = Real.exp ((c1 + c2) * ‖x‖) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc |f x * g x| = |f x| * |g x| := abs_mul _ _
    _ ≤ (C1 * Real.exp (c1 * ‖x‖)) * (C2 * Real.exp (c2 * ‖x‖)) := by
        refine mul_le_mul (h1 x) (h2 x) (abs_nonneg _) (by positivity)
    _ = C1 * C2 * (Real.exp (c1 * ‖x‖) * Real.exp (c2 * ‖x‖)) := by ring
    _ = C1 * C2 * Real.exp ((c1 + c2) * ‖x‖) := by rw [hexp]

theorem expBounded_pow (k : ℕ) : ExpBounded (fun x : ℝ => x ^ k) := by
  refine ⟨(k.factorial : ℝ), 1, zero_le_one, fun x => ?_⟩
  rw [Real.norm_eq_abs]
  have hfac : (0 : ℝ) < (k.factorial : ℝ) := by positivity
  have h := Real.pow_div_factorial_le_exp |x| (abs_nonneg x) k
  rw [div_le_iff₀ hfac] at h
  rw [abs_pow, one_mul]
  linarith [h]

theorem expBounded_poly (p : Polynomial ℝ) : ExpBounded (fun x => p.eval x) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa [Polynomial.eval_add] using hp.add hq
  | monomial k a =>
      simpa [Polynomial.eval_monomial] using (expBounded_pow k).const_mul a

theorem continuous_starobinskyV (M alpha : ℝ) : Continuous (starobinskyV M alpha) := by
  unfold starobinskyV
  fun_prop

theorem expBounded_starobinskyV (M alpha : ℝ) (hM : 0 < M) :
    ExpBounded (starobinskyV M alpha) := by
  have hs : (0 : ℝ) ≤ Real.sqrt (2 / 3) := Real.sqrt_nonneg _
  refine ⟨4 * |M ^ 4 / (16 * alpha)|, 2 * (Real.sqrt (2 / 3) / M), by positivity, fun x => ?_⟩
  rw [Real.norm_eq_abs]
  have habsu : |-(Real.sqrt (2 / 3)) * x / M| = Real.sqrt (2 / 3) / M * |x| := by
    rw [abs_div, abs_mul, abs_neg, abs_of_pos hM, abs_of_nonneg hs]
    ring
  have hexp_le : Real.exp (-(Real.sqrt (2 / 3)) * x / M)
      ≤ Real.exp (Real.sqrt (2 / 3) / M * |x|) :=
    Real.exp_le_exp.mpr (by rw [← habsu]; exact le_abs_self _)
  have hone : (1 : ℝ) ≤ Real.exp (Real.sqrt (2 / 3) / M * |x|) :=
    Real.one_le_exp (by positivity)
  have hpos : 0 < Real.exp (-(Real.sqrt (2 / 3)) * x / M) := Real.exp_pos _
  have habs : |1 - Real.exp (-(Real.sqrt (2 / 3)) * x / M)|
      ≤ 2 * Real.exp (Real.sqrt (2 / 3) / M * |x|) := by
    rw [abs_le]
    constructor <;> linarith
  have hexp2 : (Real.exp (Real.sqrt (2 / 3) / M * |x|)) ^ 2
      = Real.exp (2 * (Real.sqrt (2 / 3) / M) * |x|) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hsq : (1 - Real.exp (-(Real.sqrt (2 / 3)) * x / M)) ^ 2
      ≤ 4 * Real.exp (2 * (Real.sqrt (2 / 3) / M) * |x|) := by
    nlinarith [mul_self_le_mul_self
        (abs_nonneg (1 - Real.exp (-(Real.sqrt (2 / 3)) * x / M))) habs,
      sq_abs (1 - Real.exp (-(Real.sqrt (2 / 3)) * x / M)), hexp2]
  have hV : |starobinskyV M alpha x|
      = |M ^ 4 / (16 * alpha)| * (1 - Real.exp (-(Real.sqrt (2 / 3)) * x / M)) ^ 2 := by
    rw [starobinskyV, abs_mul]
    congr 1
    exact abs_of_nonneg (sq_nonneg _)
  rw [hV]
  have hK : (0 : ℝ) ≤ |M ^ 4 / (16 * alpha)| := abs_nonneg _
  calc |M ^ 4 / (16 * alpha)| * (1 - Real.exp (-(Real.sqrt (2 / 3)) * x / M)) ^ 2
      ≤ |M ^ 4 / (16 * alpha)| * (4 * Real.exp (2 * (Real.sqrt (2 / 3) / M) * |x|)) :=
        mul_le_mul_of_nonneg_left hsq hK
    _ = 4 * |M ^ 4 / (16 * alpha)| * Real.exp (2 * (Real.sqrt (2 / 3) / M) * |x|) := by ring

theorem ExpBounded.comp_coord {f : ℝ → ℝ} (hf : ExpBounded f) (i : Fin d) :
    ExpBounded (fun x : Vd d => f (x i)) := by
  obtain ⟨C, c, hc, h⟩ := hf
  have hC : 0 ≤ C := ExpBounded.nonneg_const h
  refine ⟨C, c, hc, fun x => ?_⟩
  have hle : ‖x i‖ ≤ ‖x‖ := PiLp.norm_apply_le x i
  calc |f (x i)| ≤ C * Real.exp (c * ‖x i‖) := h (x i)
    _ ≤ C * Real.exp (c * ‖x‖) := by gcongr

theorem continuous_scalaronSectorPotential (M alpha : ℝ) (V3 : Polynomial ℝ) :
    Continuous (scalaronSectorPotential M alpha V3) := by
  unfold scalaronSectorPotential
  exact (V3.continuous_aeval.comp (by fun_prop)).add
    ((continuous_starobinskyV M alpha).comp (by fun_prop))

theorem expBounded_scalaronSectorPotential (M alpha : ℝ) (hM : 0 < M) (V3 : Polynomial ℝ) :
    ExpBounded (scalaronSectorPotential M alpha V3) :=
  ((expBounded_poly V3).comp_coord 0).add ((expBounded_starobinskyV M alpha hM).comp_coord 1)
end BookProof.QgHermiteCore

namespace BookProof.QgHermiteFriedrichs
open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.Starobinsky
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.FriedrichsExtension
variable {d : ℕ}
variable (W : Vd d → ℝ)
theorem hermiteCore_friedrichs_extension (hWc : Continuous W) (hWb : ExpBounded W) (c : ℝ)
    (hlb : ∀ x, -c ≤ W x) :
    ∃ (Dom : Submodule ℂ (L2d d)) (A : Dom →ₗ[ℂ] L2d d),
      IsSemiboundedSelfAdjointExtension c (hamCore W hWc hWb) A :=
  SirkFriedrichsAux.friedrichs_extension_of_semibounded_below _ polyGaussCore_dense
    (hamCore_symmetricOn W hWc hWb) c (hamCore_quadForm_ge W hWc hWb c hlb)

theorem hermiteCore_friedrichs_extension_of_nonneg (hWc : Continuous W) (hWb : ExpBounded W)
    (hW0 : ∀ x, 0 ≤ W x) :
    ∃ (Dom : Submodule ℂ (L2d d)) (A : Dom →ₗ[ℂ] L2d d),
      IsPositiveSelfAdjointExtension (hamCore W hWc hWb) A :=
  SirkFriedrichsAux.friedrichs_extension_exists
    ⟨_, hamCore W hWc hWb, hamCore_symmetricOn W hWc hWb,
      hamCore_quadForm_nonneg W hWc hWb hW0⟩ polyGaussCore_dense

theorem continuous_scalaronW (M alpha : ℝ) : Continuous (scalaronW M alpha) := by
  change Continuous fun x : Vd 1 => starobinskyV M alpha (x 0)
  exact (continuous_starobinskyV M alpha).comp (by fun_prop)

theorem expBounded_scalaronW (M alpha : ℝ) (hM : 0 < M) : ExpBounded (scalaronW M alpha) := by
  change ExpBounded fun x : Vd 1 => starobinskyV M alpha (x 0)
  exact (expBounded_starobinskyV M alpha hM).comp_coord 0

theorem scalaronW_nonneg {M alpha : ℝ} (halpha : 0 < alpha) (x : Vd 1) :
    0 ≤ scalaronW M alpha x :=
  starobinskyV_nonneg halpha _

theorem qgOneParticleHermite_friedrichs (M alpha : ℝ) (hM : 0 < M) (halpha : 0 < alpha) :
    ∃ (Dom : Submodule ℂ (L2d 1)) (A : Dom →ₗ[ℂ] L2d 1),
      IsPositiveSelfAdjointExtension
        (hamCore (scalaronW M alpha) (continuous_scalaronW M alpha)
          (expBounded_scalaronW M alpha hM)) A :=
  hermiteCore_friedrichs_extension_of_nonneg _ _ _ (scalaronW_nonneg halpha)

theorem qgOneParticleSector_friedrichs (M alpha : ℝ) (hM : 0 < M) (halpha : 0 < alpha)
    (V3 : Polynomial ℝ) (c : ℝ) (hV3 : ∀ t : ℝ, -c ≤ V3.eval t) :
    ∃ (Dom : Submodule ℂ (L2d 2)) (A : Dom →ₗ[ℂ] L2d 2),
      IsSemiboundedSelfAdjointExtension c
        (hamCore (scalaronSectorPotential M alpha V3)
          (continuous_scalaronSectorPotential M alpha V3)
          (expBounded_scalaronSectorPotential M alpha hM V3)) A := by
  refine hermiteCore_friedrichs_extension _ _ _ c fun x => ?_
  have h1 := hV3 (x 0)
  have h2 := BookProof.Starobinsky.starobinskyV_nonneg (M := M) halpha (x 1)
  simp only [scalaronSectorPotential]
  linarith
end BookProof.QgHermiteFriedrichs

open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.Starobinsky
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.FriedrichsExtension
open BookProof.QgHermiteFriedrichs
variable {d : ℕ}
variable (W : Vd d → ℝ)
theorem solution (hWc : Continuous W) (hWb : ExpBounded W) (c : ℝ)
    (hlb : ∀ x, -c ≤ W x) :
    ∃ (Dom : Submodule ℂ (L2d d)) (A : Dom →ₗ[ℂ] L2d d),
      IsSemiboundedSelfAdjointExtension c (hamCore W hWc hWb) A := by
  exact BookProof.QgHermiteFriedrichs.hermiteCore_friedrichs_extension W hWc hWb c hlb
#print axioms solution
