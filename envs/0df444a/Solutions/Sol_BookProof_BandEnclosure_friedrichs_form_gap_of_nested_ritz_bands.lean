-- Prove2me | solution 1 for BookProof.BandEnclosure.friedrichs_form_gap_of_nested_ritz_bands
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:52:26.777631+00:00
-- url     : https://prove2.me/submissions/57addf1a-e9ff-42aa-aeb4-64590b5c1c47

import Definitions.Def_ChapterBandEnclosure
-- Adapted prerequisite proofs: Leonardo Pedro, timepiece 61595bc (Apache-2.0).
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Filter Topology
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
namespace SirkBandRitzAux
open BookProof.ChapterSirkRitzSpectrum BookProof.HermiteGalerkin BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit BookProof.BandEnclosure
open Filter Topology
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] {D : Submodule ℂ F}

private theorem galerkinSpan_mono (b : HilbertBasis ℕ ℂ F) {m n : ℕ} (hmn : m ≤ n) :
    galerkinSpan b m ≤ galerkinSpan b n :=
  Submodule.span_mono (Set.image_mono fun _ hi => lt_of_lt_of_le hi hmn)

private theorem basis_mem_galerkinSpan (b : HilbertBasis ℕ ℂ F) {i m : ℕ} (him : i < m) :
    b i ∈ galerkinSpan b m :=
  Submodule.subset_span ⟨i, him, rfl⟩

private theorem galerkinSpan_le_finiteModeDomain (b : HilbertBasis ℕ ℂ F) (m : ℕ) :
    galerkinSpan b m ≤ finiteModeDomain b :=
  Submodule.span_mono (by rintro x ⟨i, _, rfl⟩; exact ⟨i, rfl⟩)

private theorem finiteModeDomain_eq_iSup (b : HilbertBasis ℕ ℂ F) :
    finiteModeDomain b = ⨆ m : ℕ, galerkinSpan b m := by
  refine le_antisymm ?_ (iSup_le fun m => galerkinSpan_le_finiteModeDomain b m)
  rw [finiteModeDomain, Submodule.span_le]
  rintro x ⟨i, rfl⟩
  exact Submodule.mem_iSup_of_mem (i + 1) (basis_mem_galerkinSpan b (Nat.lt_succ_self i))

private theorem exists_mem_galerkinSpan (b : HilbertBasis ℕ ℂ F) {x : F} (hx : x ∈ finiteModeDomain b) :
    ∃ m : ℕ, x ∈ galerkinSpan b m := by
  rw [finiteModeDomain_eq_iSup] at hx
  have hmono : Monotone (fun m : ℕ => galerkinSpan b m) := fun _ _ h => galerkinSpan_mono b h
  have hdir : Directed (· ≤ ·) (fun m : ℕ => galerkinSpan b m) := hmono.directed_le
  exact (Submodule.mem_iSup_of_directed _ hdir).mp hx

private theorem ritzSet_mono (H : D →ₗ[ℂ] F) {V W : Submodule ℂ F} (hVW : V ≤ W) :
    ritzSet H V ⊆ ritzSet H W := by
  rintro t ⟨x, hxV, hx1, rfl⟩
  exact ⟨x, hVW hxV, hx1, rfl⟩

private theorem ritzSet_bddBelow (H : D →ₗ[ℂ] F) (hpos : ∀ x : D, 0 ≤ quadForm H x)
    (V : Submodule ℂ F) : BddBelow (ritzSet H V) := by
  refine ⟨0, ?_⟩
  rintro t ⟨x, _, _, rfl⟩
  exact hpos x

private theorem ritzInf_antitone (H : D →ₗ[ℂ] F) (hpos : ∀ x : D, 0 ≤ quadForm H x)
    {V W : Submodule ℂ F} (hVW : V ≤ W) (hV : (ritzSet H V).Nonempty) :
    ritzInf H W ≤ ritzInf H V :=
  csInf_le_csInf (ritzSet_bddBelow H hpos W) hV (ritzSet_mono H hVW)

private theorem ritzInf_nonneg (H : D →ₗ[ℂ] F) (hpos : ∀ x : D, 0 ≤ quadForm H x)
    (V : Submodule ℂ F) (hV : (ritzSet H V).Nonempty) : 0 ≤ ritzInf H V :=
  le_csInf hV (by rintro t ⟨x, _, _, rfl⟩; exact hpos x)

private theorem ritzInf_tendsto_domainInf (b : HilbertBasis ℕ ℂ F) (H : finiteModeDomain b →ₗ[ℂ] F)
    (hpos : ∀ x : finiteModeDomain b, 0 ≤ quadForm H x) :
    Tendsto (fun m : ℕ => ritzInf H (galerkinSpan b (m + 1))) atTop
      (nhds (ritzInf H (finiteModeDomain b))) := by
  set a : ℕ → ℝ := fun m => ritzInf H (galerkinSpan b (m + 1)) with ha
  -- the first basis vector is a unit vector of every truncation subspace
  have hb0mem : b 0 ∈ finiteModeDomain b := Submodule.subset_span ⟨0, rfl⟩
  have hb0norm : ‖b 0‖ = 1 := b.orthonormal.1 0
  have hne : ∀ m : ℕ, (ritzSet H (galerkinSpan b (m + 1))).Nonempty := by
    intro m
    refine ⟨quadForm H ⟨b 0, hb0mem⟩, ⟨b 0, hb0mem⟩, ?_, hb0norm, rfl⟩
    exact galerkinSpan_mono b (Nat.succ_le_succ (Nat.zero_le m))
      (basis_mem_galerkinSpan b Nat.zero_lt_one)
  have hsub : ∀ m : ℕ, ritzSet H (galerkinSpan b (m + 1)) ⊆ ritzSet H (finiteModeDomain b) :=
    fun m => ritzSet_mono H (galerkinSpan_le_finiteModeDomain b (m + 1))
  -- the sequence of Ritz values is antitone and bounded below
  have hanti : Antitone a := by
    intro p q hpq
    exact ritzInf_antitone H hpos (galerkinSpan_mono b (Nat.succ_le_succ hpq)) (hne p)
  have hnonneg : ∀ m : ℕ, 0 ≤ a m := fun m => ritzInf_nonneg H hpos _ (hne m)
  have hbdd : BddBelow (Set.range a) := ⟨0, by rintro t ⟨m, rfl⟩; exact hnonneg m⟩
  have hlim := tendsto_atTop_ciInf hanti hbdd
  -- and its limit is the infimum of the energy over the whole domain
  have hSne : (ritzSet H (finiteModeDomain b)).Nonempty := (hne 0).mono (hsub 0)
  have hkey : (⨅ m : ℕ, a m) = ritzInf H (finiteModeDomain b) := by
    refine le_antisymm ?_ ?_
    · refine le_csInf hSne ?_
      rintro t ⟨x, _, hx1, rfl⟩
      obtain ⟨m, hm⟩ := exists_mem_galerkinSpan b x.2
      have hmem : quadForm H x ∈ ritzSet H (galerkinSpan b (m + 1)) :=
        ⟨x, galerkinSpan_mono b (Nat.le_succ m) hm, hx1, rfl⟩
      refine le_trans (ciInf_le hbdd m) ?_
      exact csInf_le (ritzSet_bddBelow H hpos _) hmem
    · refine le_ciInf fun m => ?_
      exact csInf_le_csInf (ritzSet_bddBelow H hpos _) (hne m) (hsub m)
  rw [← hkey]
  exact hlim

private theorem nestedBands_le {lo hi : ℕ → ℝ} (h : NestedBands lo hi) {m n : ℕ} (hmn : m ≤ n) :
    Set.Icc (lo n) (hi n) ⊆ Set.Icc (lo m) (hi m) := by
  induction n, hmn using Nat.le_induction with
  | base => exact subset_rfl
  | succ n _ ih => exact (h n).trans ih

private theorem band_enclosure_of_nested {lo hi a : ℕ → ℝ} {lam : ℝ}
    (hnest : NestedBands lo hi) (hmem : ∀ m, a m ∈ Set.Icc (lo m) (hi m))
    (hconv : Tendsto a atTop (𝓝 lam)) :
    ∀ m, lam ∈ Set.Icc (lo m) (hi m) := by
  intro m
  have hev : ∀ᶠ n in atTop, a n ∈ Set.Icc (lo m) (hi m) := by
    filter_upwards [eventually_ge_atTop m] with n hn
    exact nestedBands_le hnest hn (hmem n)
  exact ⟨ge_of_tendsto hconv (hev.mono fun _ hn => hn.1),
    le_of_tendsto hconv (hev.mono fun _ hn => hn.2)⟩

end SirkBandRitzAux
namespace SirkBandFormAux
open BookProof.FarisLavine BookProof.HermiteGalerkin
open SirkBandRitzAux
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] {Dom : Submodule ℂ F}
private theorem quadForm_real_smul {D : Submodule ℂ F} (H : D →ₗ[ℂ] F) (c : ℝ) (x : D) :
    quadForm H ((c : ℂ) • x) = c ^ 2 * quadForm H x := by
  have h : (inner ℂ (((c : ℂ) • x : D) : F) (H ((c : ℂ) • x)) : ℂ)
      = ((c ^ 2 : ℝ) : ℂ) * inner ℂ (x : F) (H x) := by
    rw [map_smul, Submodule.coe_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    push_cast
    ring
  rw [quadForm, quadForm, h, Complex.re_ofReal_mul]

private theorem quadForm_ge_of_le_ritzInf {D : Submodule ℂ F} (H : D →ₗ[ℂ] F)
    (hpos : ∀ x : D, 0 ≤ quadForm H x) {mu : ℝ} (hmu : mu ≤ ritzInf H D) (x : D) :
    mu * ‖(x : F)‖ ^ 2 ≤ quadForm H x := by
  rcases eq_or_ne ((x : F)) 0 with hx | hx
  · have hx0 : x = 0 := Subtype.ext hx
    simp [hx0, quadForm]
  · have hnpos : 0 < ‖(x : F)‖ := norm_pos_iff.mpr hx
    set c : ℝ := ‖(x : F)‖⁻¹ with hc
    have hcpos : 0 < c := inv_pos.mpr hnpos
    have hunit : ‖(((c : ℂ) • x : D) : F)‖ = 1 := by
      rw [Submodule.coe_smul, norm_smul]
      simp [hc, hnpos.ne']
    have hmem : quadForm H ((c : ℂ) • x) ∈ ritzSet H D :=
      ⟨(c : ℂ) • x, ((c : ℂ) • x : D).2, hunit, rfl⟩
    have hle : ritzInf H D ≤ quadForm H ((c : ℂ) • x) :=
      csInf_le (ritzSet_bddBelow H hpos D) hmem
    rw [quadForm_real_smul] at hle
    have hsq : c ^ 2 * ‖(x : F)‖ ^ 2 = 1 := by
      rw [hc, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hnpos.ne')]
    have h2 := mul_le_mul_of_nonneg_right (hmu.trans hle) (sq_nonneg ‖(x : F)‖)
    have h3 : c ^ 2 * quadForm H x * ‖(x : F)‖ ^ 2
        = (c ^ 2 * ‖(x : F)‖ ^ 2) * quadForm H x := by ring
    rw [h3, hsq, one_mul] at h2
    exact h2

end SirkBandFormAux

-- Generated from ChapterBandEnclosure.lean — theorem BookProof.BandEnclosure.friedrichs_form_gap_of_nested_ritz_bands
open BookProof.BandEnclosure










noncomputable section

open Filter Topology


open BookProof.FockOneParticleGap BookProof.FockSecondQuantization
open BookProof.ChapterH6 BookProof.ChapterH8















open BookProof.HermiteGalerkin BookProof.YangMillsFriedrichs
open BookProof.YangMillsFriedrichsLimit BookProof.ChapterSirkRitzSpectrum

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]













open BookProof.FarisLavine BookProof.HermiteGalerkin BookProof.YangMillsFriedrichs
open BookProof.HashimotoShiftInvert BookProof.FriedrichsExtension


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
theorem solution (b : HilbertBasis ℕ ℂ F)
    (H : finiteModeDomain b →ₗ[ℂ] F) (hsym : SymmetricOn (finiteModeDomain b) H)
    (hpos : ∀ x : finiteModeDomain b, 0 ≤ quadForm H x)
    {lo hi : ℕ → ℝ} {mu : ℝ} (hnest : NestedBands lo hi)
    (hritz : ∀ m, ritzInf H (galerkinSpan b (m + 1)) ∈ Set.Icc (lo m) (hi m))
    {m₀ : ℕ} (hlo : mu ≤ lo m₀) :
    (∀ m, ritzInf H (finiteModeDomain b) ∈ Set.Icc (lo m) (hi m)) ∧
      mu ≤ ritzInf H (finiteModeDomain b) ∧
      ∃ (Dom : Submodule ℂ F) (A : Dom →ₗ[ℂ] F) (S : F →L[ℂ] F),
        IsPositiveSelfAdjointExtension H A ∧ IsShiftInvert A 1 S ∧ IsSelfAdjoint S ∧
          ∀ y : Dom, mu * ‖(y : F)‖ ^ 2 ≤ quadForm A y := by
  have hband := SirkBandRitzAux.band_enclosure_of_nested hnest hritz
    (SirkBandRitzAux.ritzInf_tendsto_domainInf b H hpos)
  have hmu : mu ≤ ritzInf H (finiteModeDomain b) := hlo.trans (hband m₀).1
  refine ⟨hband, hmu, ?_⟩
  have hdense : Dense ((finiteModeDomain b : Submodule ℂ F) : Set F) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span
  exact SirkFriedrichsAux.friedrichs_extension_form_gap ⟨finiteModeDomain b, H, hsym, hpos⟩
    hdense (SirkBandFormAux.quadForm_ge_of_le_ritzInf H hpos hmu)
#print axioms solution
