-- Prove2me | solution 1 for BookProof.FriedrichsFormGap.friedrichs_extension_form_gap
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T17:16:41.234736+00:00
-- url     : https://prove2.me/submissions/b1bf1096-6f2b-429e-a626-209746c71a7f

/- Adapted from Leonardo Pedro, timepiece commit 61595bc, Apache-2.0. -/
import Mathlib
import Definitions.Def_ChapterNavierStokesFockSpace
import Definitions.Def_ChapterFriedrichsFormGap
import Definitions.Def_ChapterBandEnclosure
noncomputable section
set_option maxRecDepth 2000
set_option maxHeartbeats 1500000
namespace BookProof.NavierStokesFlow.FockOfFock
open BookProof.NavierStokesFlow.FullEsa
variable {ι : Type*}
theorem lpBasis_coe [DecidableEq ι] (i j : ι) :
    (((lpBasis i : lpFiniteModes ι) : lp (fun _ : ι => ℂ) 2) : ι → ℂ) j
      = if j = i then 1 else 0 := by
  by_cases h : j = i
  · subst h; simp [lpBasis, lp.single_apply]
  · simp [lpBasis, lp.single_apply, h]
variable {M : Type*} [DecidableEq M]
theorem fockBasis_coe (n k : Conf M) :
    (((fockBasis n : FockDom M) : FockL2 M) : Conf M → ℂ) k = if k = n then 1 else 0 :=
  lpBasis_coe n k

theorem add_single_sub_single (m : M) (n : Conf M) :
    (n + Finsupp.single m 1 : Conf M) - Finsupp.single m 1 = n := by
  ext j
  rcases eq_or_ne j m with rfl | hj
  · simp
  · simp

@[simp] theorem annih_coe (m : M) (f : FockDom M) (n : Conf M) :
    (((annih m f : FockDom M) : FockL2 M) : Conf M → ℂ) n
      = (Real.sqrt (n m + 1) : ℂ) * ((f : FockL2 M) : Conf M → ℂ) (n + Finsupp.single m 1) := rfl

@[simp] theorem creat_coe (m : M) (f : FockDom M) (n : Conf M) :
    (((creat m f : FockDom M) : FockL2 M) : Conf M → ℂ) n
      = (Real.sqrt (n m) : ℂ) * ((f : FockL2 M) : Conf M → ℂ) (n - Finsupp.single m 1) := rfl

theorem annih_basis (m : M) (n : Conf M) :
    annih m (fockBasis n) = ((Real.sqrt (n m) : ℝ) : ℂ) • fockBasis (n - Finsupp.single m 1) := by
  ext k
  change (Real.sqrt ((k m : ℝ) + 1) : ℂ) * (((fockBasis n : FockDom M) : FockL2 M) : Conf M → ℂ) (k + Finsupp.single m 1) = (Real.sqrt (n m : ℝ) : ℂ) * (((fockBasis (n - Finsupp.single m 1) : FockDom M) : FockL2 M) : Conf M → ℂ) k
  rcases eq_or_ne (k + Finsupp.single m 1) n with hk | hk
  · have hkm : k = n - Finsupp.single m 1 := by
      rw [← hk, add_single_sub_single]
    have hnm : (n m : ℝ) = (k m : ℝ) + 1 := by
      rw [← hk]; push_cast; simp
    subst hkm
    simp [annih_coe, fockBasis_coe, hk, hnm]
  · have hkne : k ≠ n - Finsupp.single m 1 ∨ (n m) = 0 := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨hk1, hk2⟩ := hcon
      apply hk
      rw [hk1]
      exact sub_single_add_single (by omega)
    simp only [annih_coe, fockBasis_coe, hk, if_false, mul_zero, Submodule.coe_smul]
    rcases hkne with h | h
    · simp [fockBasis_coe, h]
    · simp [h]

theorem creat_basis (m : M) (n : Conf M) :
    creat m (fockBasis n)
      = ((Real.sqrt (n m + 1) : ℝ) : ℂ) • fockBasis (n + Finsupp.single m 1) := by
  ext k
  change (Real.sqrt (k m : ℝ) : ℂ) * (((fockBasis n : FockDom M) : FockL2 M) : Conf M → ℂ) (k - Finsupp.single m 1) = (Real.sqrt ((n m : ℝ) + 1) : ℂ) * (((fockBasis (n + Finsupp.single m 1) : FockDom M) : FockL2 M) : Conf M → ℂ) k
  rcases eq_or_ne k (n + Finsupp.single m 1) with rfl | hk
  · have h1 : (n + Finsupp.single m 1 : Conf M) - Finsupp.single m 1 = n :=
      add_single_sub_single m n
    have h2 : ((n + Finsupp.single m 1 : Conf M) m : ℝ) = (n m : ℝ) + 1 := by push_cast; simp
    simp [creat_coe, fockBasis_coe, h1]
  · have hne : k - Finsupp.single m 1 ≠ n ∨ k m = 0 := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨h1, h2⟩ := hcon
      apply hk
      rw [← h1]
      exact (sub_single_add_single (by omega)).symm
    simp only [creat_coe, fockBasis_coe, Submodule.coe_smul]
    have hr : (((fockBasis (n + Finsupp.single m 1) : FockDom M) : FockL2 M) : Conf M → ℂ) k = 0
        := by
      rw [fockBasis_coe, if_neg hk]
    rcases hne with h | h
    · rw [if_neg h, mul_zero]
      simp [hr, hk]
    · rw [h]
      simp [hr, hk]

theorem creat_vacuum (m : M) :
    creat m (vacuum : FockDom M) = fockBasis (Finsupp.single m 1) := by
  rw [vacuum, creat_basis]
  simp
variable {J K : Type*} [DecidableEq J] [DecidableEq K]
theorem outerOneParticle (j : J) (c : Conf K) :
    creat (j, c) (vacuum : FockOfFockDom J K) = fockBasis (Finsupp.single (j, c) 1) :=
  creat_vacuum _
end BookProof.NavierStokesFlow.FockOfFock
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

theorem friedrichs_extension_form_gap (P : PosSymOp F) (hdense : Dense (P.dom : Set F))
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
-- Generated from ChapterFriedrichsFormGap.lean — theorem BookProof.FriedrichsFormGap.friedrichs_extension_form_gap
open BookProof.FriedrichsFormGap









open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert
open BookProof.FriedrichsExtension BookProof.FriedrichsExtension.FormDom

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
theorem solution (P : PosSymOp F) (hdense : Dense (P.dom : Set F))
    {mu : ℝ} (hmu : ∀ x : P.dom, mu * ‖(x : F)‖ ^ 2 ≤ quadForm P.op x) :
    ∃ (Dom : Submodule ℂ F) (A : Dom →ₗ[ℂ] F) (S : F →L[ℂ] F),
      IsPositiveSelfAdjointExtension P.op A ∧ IsShiftInvert A 1 S ∧
        IsSelfAdjoint S ∧ (∀ y : Dom, mu * ‖(y : F)‖ ^ 2 ≤ quadForm A y) := by
  exact SirkFriedrichsAux.friedrichs_extension_form_gap P hdense hmu
#print axioms solution
