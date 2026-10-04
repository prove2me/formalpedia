-- Prove2me | solution 1 for BookProof.FriedrichsExtension.weyl_hashimoto_selects_friedrichs
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T02:52:13.98454+00:00
-- url     : https://prove2.me/submissions/1c96941d-9569-47fa-85ae-314c38817cf4

import Mathlib
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichs

set_option autoImplicit false

open BookProof.HashimotoShiftInvert BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HermiteGalerkin Filter Topology in
theorem P2M_1d5acad2_shift_ge {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {Dom : Submodule ℂ F} {A : Dom →ₗ[ℂ] F}
    (hpos : ∀ x : Dom, 0 ≤ quadForm A x) {γ : ℝ} (hγ : 0 < γ) (x : Dom) :
    γ * ‖(x : F)‖ ≤ ‖shiftMap A γ x‖ := by
  have hre : (inner ℂ (x : F) (shiftMap A γ x) : ℂ).re = quadForm A x + γ * ‖(x : F)‖ ^ 2 := by
    have : shiftMap A γ x = A x + (γ : ℂ) • (x : F) := rfl
    rw [this, inner_add_right, inner_smul_right, Complex.add_re, inner_self_eq_norm_sq_to_K]
    simp [quadForm, ← Complex.ofReal_pow]
  have h2 : (inner ℂ (x : F) (shiftMap A γ x) : ℂ).re ≤ ‖(x : F)‖ * ‖shiftMap A γ x‖ :=
    le_trans (Complex.re_le_norm _) (norm_inner_le_norm _ _)
  rw [hre] at h2
  have hq := hpos x
  rcases eq_or_lt_of_le (norm_nonneg (x : F)) with h0 | hpx
  · rw [← h0]; simp
  · have : γ * ‖(x : F)‖ ^ 2 ≤ ‖(x : F)‖ * ‖shiftMap A γ x‖ := by linarith
    have h3 : ‖(x : F)‖ * (γ * ‖(x : F)‖) ≤ ‖(x : F)‖ * ‖shiftMap A γ x‖ := by nlinarith
    exact le_of_mul_le_mul_left h3 hpx

open BookProof.HashimotoShiftInvert BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HermiteGalerkin Filter Topology in
theorem P2M_1d5acad2_closed {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {Dom : Submodule ℂ F} {A : Dom →ₗ[ℂ] F} (hsym : SymmetricOn Dom A)
    (hpos : ∀ x : Dom, 0 ≤ quadForm A x)
    (hsa : ∀ w u : F, (∀ v : Dom, (inner ℂ (A v) w : ℂ) = inner ℂ (v : F) u) →
      ∃ h : w ∈ Dom, A ⟨w, h⟩ = u)
    {γ : ℝ} (hγ : 0 < γ) : IsClosed ((shiftRange A γ : Submodule ℂ F) : Set F) := by
  refine IsSeqClosed.isClosed ?_
  intro u p hu hup
  choose x hx using hu
  have hcauchy : CauchySeq (fun n => ((x n : F))) := by
    have hucauchy : CauchySeq u := hup.cauchySeq
    rw [Metric.cauchySeq_iff] at hucauchy ⊢
    intro eps heps
    obtain ⟨N, hN⟩ := hucauchy (γ * eps) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hb : γ * ‖((x m - x n : Dom) : F)‖ ≤ ‖shiftMap A γ (x m - x n)‖ :=
      P2M_1d5acad2_shift_ge hpos hγ _
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
  have hAconv : Tendsto (fun n => A (x n)) atTop (nhds (p - (γ : ℂ) • w)) := by
    have hval : ∀ n, A (x n) = u n - (γ : ℂ) • ((x n : F)) := by
      intro n
      have hn : A (x n) + (γ : ℂ) • ((x n : F)) = u n := hx n
      rw [← hn]; abel
    simp only [hval]
    exact hup.sub (hw.const_smul (γ : ℂ))
  obtain ⟨hwmem, hAw⟩ := closed_of_selfAdjointCriterion hsym hsa hw hAconv
  refine ⟨⟨w, hwmem⟩, ?_⟩
  show A ⟨w, hwmem⟩ + (γ : ℂ) • w = p
  rw [hAw]
  abel


open BookProof.HashimotoShiftInvert BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HermiteGalerkin Filter Topology in
theorem P2M_1d5acad2_orth {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {Dom : Submodule ℂ F} {A : Dom →ₗ[ℂ] F}
    (hpos : ∀ x : Dom, 0 ≤ quadForm A x)
    (hsa : ∀ w u : F, (∀ v : Dom, (inner ℂ (A v) w : ℂ) = inner ℂ (v : F) u) →
      ∃ h : w ∈ Dom, A ⟨w, h⟩ = u)
    {γ : ℝ} (hγ : 0 < γ) : (shiftRange A γ)ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro w hw
  have hip : ∀ v : Dom, (inner ℂ (A v) w : ℂ) = inner ℂ (v : F) ((-(γ : ℂ)) • w) := by
    intro v
    have hmem : shiftMap A γ v ∈ shiftRange A γ := ⟨v, rfl⟩
    have h0 : (inner ℂ (shiftMap A γ v) w : ℂ) = 0 := hw _ hmem
    have happ : shiftMap A γ v = A v + (γ : ℂ) • (v : F) := rfl
    rw [happ, inner_add_left, inner_smul_left] at h0
    rw [inner_smul_right]
    simp only [Complex.conj_ofReal] at h0
    linear_combination h0
  obtain ⟨hwmem, hAw⟩ := hsa w ((-(γ : ℂ)) • w) hip
  have hq := hpos ⟨w, hwmem⟩
  unfold quadForm at hq
  rw [hAw] at hq
  simp only [inner_smul_right, inner_self_eq_norm_sq_to_K] at hq
  have hq' : -γ * ‖w‖ ^ 2 ≥ 0 := by
    simpa [← Complex.ofReal_pow, Complex.mul_re] using hq
  have hn : ‖w‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖w‖]
  have : ‖w‖ = 0 := by nlinarith [norm_nonneg w]
  simpa using this

open BookProof.HashimotoShiftInvert BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HermiteGalerkin Filter Topology in
theorem P2M_1d5acad2_surj {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {Dom : Submodule ℂ F} {A : Dom →ₗ[ℂ] F} (hsym : SymmetricOn Dom A)
    (hpos : ∀ x : Dom, 0 ≤ quadForm A x)
    (hsa : ∀ w u : F, (∀ v : Dom, (inner ℂ (A v) w : ℂ) = inner ℂ (v : F) u) →
      ∃ h : w ∈ Dom, A ⟨w, h⟩ = u)
    {γ : ℝ} (hγ : 0 < γ) : Function.Surjective (shiftMap A γ) := by
  have hclosed : IsClosed ((shiftRange A γ : Submodule ℂ F) : Set F) :=
    P2M_1d5acad2_closed hsym hpos hsa hγ
  haveI : CompleteSpace (shiftRange A γ) := hclosed.completeSpace_coe
  have htop : shiftRange A γ = ⊤ := by
    have h1 := Submodule.orthogonal_orthogonal (shiftRange A γ)
    rw [P2M_1d5acad2_orth hpos hsa hγ, Submodule.bot_orthogonal_eq_top] at h1
    exact h1.symm
  intro u
  have hmem : u ∈ shiftRange A γ := by rw [htop]; trivial
  exact hmem


open BookProof.HashimotoShiftInvert BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HermiteGalerkin Filter Topology in
theorem P2M_1d5acad2_exists {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {Dom : Submodule ℂ F} {A : Dom →ₗ[ℂ] F} (hpos : ∀ x : Dom, 0 ≤ quadForm A x)
    {γ : ℝ} (hγ : 0 < γ) (hsurj : Function.Surjective (shiftMap A γ)) :
    ∃ R : F →L[ℂ] F, IsShiftInvert A γ R := by
  have hinj : Function.Injective (shiftMap A γ) := by
    intro x y hxy
    have h := P2M_1d5acad2_shift_ge hpos hγ (x - y)
    rw [map_sub, hxy, sub_self, norm_zero] at h
    have hx : ‖((x - y : Dom) : F)‖ = 0 :=
      le_antisymm (by nlinarith [norm_nonneg ((x - y : Dom) : F)]) (norm_nonneg _)
    have hz : ((x - y : Dom) : F) = 0 := norm_eq_zero.mp hx
    have hz' : x - y = 0 := Subtype.ext (by simpa using hz)
    exact sub_eq_zero.mp hz'
  let f : Dom ≃ₗ[ℂ] F := LinearEquiv.ofBijective (shiftMap A γ) ⟨hinj, hsurj⟩
  have hf : ∀ x : Dom, f x = shiftMap A γ x := fun x => rfl
  let R0 : F →ₗ[ℂ] F := Dom.subtype ∘ₗ (f.symm : F →ₗ[ℂ] Dom)
  have hR0 : ∀ u : F, R0 u = ((f.symm u : Dom) : F) := fun u => rfl
  have hbound : ∀ u : F, ‖R0 u‖ ≤ γ⁻¹ * ‖u‖ := by
    intro u
    have h := P2M_1d5acad2_shift_ge hpos hγ (f.symm u)
    rw [← hf, LinearEquiv.apply_symm_apply] at h
    rw [hR0, le_inv_mul_iff₀ hγ]
    exact h
  refine ⟨LinearMap.mkContinuous R0 γ⁻¹ hbound, ?_, ?_⟩
  · intro x
    rw [LinearMap.mkContinuous_apply, hR0, ← hf, LinearEquiv.symm_apply_apply]
  · intro u
    refine ⟨by rw [LinearMap.mkContinuous_apply, hR0]; exact (f.symm u).2, ?_⟩
    have : (⟨(LinearMap.mkContinuous R0 γ⁻¹ hbound) u, by
        rw [LinearMap.mkContinuous_apply, hR0]; exact (f.symm u).2⟩ : Dom) = f.symm u := by
      apply Subtype.ext
      exact (LinearMap.mkContinuous_apply R0 γ⁻¹ hbound u).trans (hR0 u)
    rw [this, ← hf, LinearEquiv.apply_symm_apply]

open BookProof.HashimotoShiftInvert BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HermiteGalerkin Filter Topology in
theorem P2M_1d5acad2_selfadj {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {Dom : Submodule ℂ F} {A : Dom →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F}
    (h : IsShiftInvert A γ R) (hsym : SymmetricOn Dom A) : IsSelfAdjoint R := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro u v
  obtain ⟨hu, hu'⟩ := h.2 u
  obtain ⟨hv, hv'⟩ := h.2 v
  have key := hsym ⟨R u, hu⟩ ⟨R v, hv⟩
  simp only [ContinuousLinearMap.coe_coe]
  conv_lhs => rw [← hv']
  conv_rhs => rw [← hu']
  simp only [shiftMap, LinearMap.add_apply, LinearMap.smul_apply, Submodule.subtype_apply,
    inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  rw [key]

open BookProof.HashimotoShiftInvert BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HermiteGalerkin Filter Topology in
theorem P2M_1d5acad2_determines {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {Dom₁ Dom₂ : Submodule ℂ F} {A₁ : Dom₁ →ₗ[ℂ] F}
    {A₂ : Dom₂ →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F}
    (h₁ : IsShiftInvert A₁ γ R) (h₂ : IsShiftInvert A₂ γ R) :
    Dom₁ = Dom₂ ∧ ∀ (x : F) (hx₁ : x ∈ Dom₁) (hx₂ : x ∈ Dom₂), A₁ ⟨x, hx₁⟩ = A₂ ⟨x, hx₂⟩ := by
  have key : ∀ {D₁ D₂ : Submodule ℂ F} {B₁ : D₁ →ₗ[ℂ] F} {B₂ : D₂ →ₗ[ℂ] F},
      IsShiftInvert B₁ γ R → IsShiftInvert B₂ γ R → D₁ ≤ D₂ := by
    intro D₁ D₂ B₁ B₂ g₁ g₂ x hx
    obtain ⟨h, -⟩ := g₂.2 (shiftMap B₁ γ ⟨x, hx⟩)
    rwa [g₁.1 ⟨x, hx⟩] at h
  refine ⟨le_antisymm (key h₁ h₂) (key h₂ h₁), ?_⟩
  intro x hx₁ hx₂
  have inj : ∀ u v : F, R u = R v → u = v := by
    intro u v huv
    obtain ⟨hu, hu'⟩ := h₁.2 u
    obtain ⟨hv, hv'⟩ := h₁.2 v
    rw [← hu', ← hv']
    congr 1
    exact Subtype.ext huv
  have e : shiftMap A₁ γ ⟨x, hx₁⟩ = shiftMap A₂ γ ⟨x, hx₂⟩ :=
    inj _ _ (by rw [h₁.1, h₂.1])
  simpa [shiftMap] using e

open BookProof.HashimotoShiftInvert BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HermiteGalerkin Filter Topology in
theorem P2M_1d5acad2_proj_tendsto {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (b : HilbertBasis ℕ ℂ F) (x : F) :
    Tendsto (fun m : ℕ => (galerkinSpan b m).starProjection x) atTop (𝓝 x) := by
  refine Submodule.starProjection_tendsto_self (galerkinSpan b) ?_ x ?_
  · intro m n hmn
    apply Submodule.span_mono
    apply Set.image_mono
    intro i hi
    exact lt_of_lt_of_le hi hmn
  · rw [← b.dense_span]
    apply Submodule.topologicalClosure_mono
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine (le_iSup (fun m => galerkinSpan b m) (i + 1)) ?_
    exact Submodule.subset_span ⟨i, Nat.lt_succ_self i, rfl⟩

open BookProof.HashimotoShiftInvert BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HermiteGalerkin Filter Topology in
theorem P2M_1d5acad2_comp_tendsto {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (T : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F) (u : F) :
    Tendsto (fun m : ℕ => galerkinCompression T b m u) atTop (𝓝 (T u)) := by
  have h1 : Tendsto (fun m : ℕ => T ((galerkinSpan b m).starProjection u)) atTop (𝓝 (T u)) :=
    (T.continuous.tendsto u).comp (P2M_1d5acad2_proj_tendsto b u)
  have h2 := P2M_1d5acad2_proj_tendsto b (T u)
  rw [tendsto_iff_norm_sub_tendsto_zero] at h1 h2 ⊢
  have h3 : Tendsto (fun m : ℕ => ‖T ((galerkinSpan b m).starProjection u) - T u‖ +
      ‖(galerkinSpan b m).starProjection (T u) - T u‖) atTop (𝓝 0) := by
    simpa using h1.add h2
  refine squeeze_zero (fun _ => norm_nonneg _) (fun m => ?_) h3
  have he : galerkinCompression T b m u - T u =
      (galerkinSpan b m).starProjection (T ((galerkinSpan b m).starProjection u) - T u) +
        ((galerkinSpan b m).starProjection (T u) - T u) := by
    rw [map_sub]
    simp only [galerkinCompression, ContinuousLinearMap.comp_apply]
    abel
  rw [he]
  refine le_trans (norm_add_le _ _) ?_
  gcongr
  exact Submodule.norm_starProjection_apply_le _ _


open BookProof.FriedrichsExtension BookProof.FriedrichsExtension.FormDom in
theorem P2M_1d5acad2_formExt_coe {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (P : PosSymOp F) (z : FormDom P) :
    formExt P (z : FormSpace P) = toAmbient z := by
  have hu : IsUniformInducing (UniformSpace.Completion.toComplL (𝕜 := ℂ) (E := FormDom P)) := by
    rw [UniformSpace.Completion.coe_toComplL]
    exact UniformSpace.Completion.isUniformInducing_coe _
  have h := ContinuousLinearMap.extend_eq (f := incl P)
    (denseRange_toComplL P) hu z
  rw [UniformSpace.Completion.coe_toComplL] at h
  exact h

open BookProof.FriedrichsExtension BookProof.FriedrichsExtension.FormDom in
theorem P2M_1d5acad2_S_apply {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (P : PosSymOp F) (u : F) :
    friedrichsResolvent P u = formExt P (formRiesz P u) := rfl

open BookProof.FriedrichsExtension BookProof.FriedrichsExtension.FormDom in
theorem P2M_1d5acad2_shift {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (P : PosSymOp F) (x : P.dom) :
    friedrichsResolvent P ((x : F) + P.op x) = (x : F) := by
  let y : FormDom P := x
  have hR : formRiesz P ((x : F) + P.op x) = (y : FormSpace P) := by
    refine ext_inner_right ℂ (fun k => ?_)
    rw [formRiesz_spec]
    induction k using UniformSpace.Completion.induction_on with
    | hp =>
      exact isClosed_eq (continuous_const.inner (formExt P).continuous)
        (continuous_const.inner continuous_id)
    | ih z =>
      rw [P2M_1d5acad2_formExt_coe, UniformSpace.Completion.inner_coe, inner_def, inner_add_left]
      congr 1
      exact P.sym x (toDom z)
  show formExt P (formRiesz P ((x : F) + P.op x)) = (x : F)
  rw [hR, P2M_1d5acad2_formExt_coe]
  rfl

open BookProof.FriedrichsExtension BookProof.FriedrichsExtension.FormDom in
theorem P2M_1d5acad2_inner_coe {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (P : PosSymOp F) (y : FormDom P) (k : FormSpace P) :
    (inner ℂ (y : FormSpace P) k : ℂ)
      = inner ℂ (toAmbient y + P.op (toDom y)) (formExt P k) := by
  induction k using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (continuous_const.inner continuous_id)
      (continuous_const.inner (formExt P).continuous)
  | ih z =>
    rw [P2M_1d5acad2_formExt_coe, UniformSpace.Completion.inner_coe, inner_def, inner_add_left]
    congr 1
    exact (P.sym (toDom y) (toDom z)).symm

open BookProof.FriedrichsExtension BookProof.FriedrichsExtension.FormDom in
theorem P2M_1d5acad2_S_selfadj {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (P : PosSymOp F) : IsSelfAdjoint (friedrichsResolvent P) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro u v
  simp only [ContinuousLinearMap.coe_coe]
  rw [← inner_conj_symm, P2M_1d5acad2_S_apply, P2M_1d5acad2_S_apply, ← formRiesz_spec,
    ← formRiesz_spec, inner_conj_symm]

open BookProof.FriedrichsExtension BookProof.FriedrichsExtension.FormDom in
theorem P2M_1d5acad2_S_pos {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (P : PosSymOp F) (u : F) :
    (1 : ℝ) * ‖friedrichsResolvent P u‖ ^ 2 ≤ (inner ℂ (friedrichsResolvent P u) u : ℂ).re := by
  rw [← inner_conj_symm, Complex.conj_re, P2M_1d5acad2_S_apply, ← formRiesz_spec,
    re_inner_self, one_mul]
  have h1 := norm_formExt_apply_le P (formRiesz P u)
  have h2 := norm_nonneg (formExt P (formRiesz P u))
  nlinarith

open BookProof.FriedrichsExtension BookProof.FriedrichsExtension.FormDom in
theorem P2M_1d5acad2_S_inj {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (P : PosSymOp F) (hd : P.dom.topologicalClosure = ⊤) :
    Function.Injective (friedrichsResolvent P) := by
  rw [injective_iff_map_eq_zero]
  intro u hu
  have horth : u ∈ P.domᗮ := by
    rw [Submodule.mem_orthogonal]
    intro v hv
    let y : FormDom P := (⟨v, hv⟩ : P.dom)
    have h1 : (inner ℂ u (formExt P (y : FormSpace P)) : ℂ)
        = inner ℂ (formRiesz P u) (y : FormSpace P) := (formRiesz_spec P u _).symm
    rw [← inner_conj_symm (formRiesz P u), P2M_1d5acad2_inner_coe, ← P2M_1d5acad2_S_apply, hu,
      inner_zero_right, map_zero, P2M_1d5acad2_formExt_coe] at h1
    have h2 : toAmbient y = v := rfl
    rw [h2] at h1
    rw [← inner_conj_symm, h1, map_zero]
  rw [Submodule.topologicalClosure_eq_top_iff.mp hd] at horth
  exact (Submodule.mem_bot ℂ).mp horth

open BookProof.HashimotoShiftInvert in
theorem P2M_1d5acad2_adj {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F]
    (R : F →L[ℂ] F) (hinj : Function.Injective R)
    (γ : ℝ) (hR : IsSelfAdjoint R) (w u : F)
    (hw : ∀ v : LinearMap.range (R : F →ₗ[ℂ] F),
      (inner ℂ (invShiftOperator R hinj γ v) w : ℂ) = inner ℂ (v : F) u) :
    ∃ h : w ∈ LinearMap.range (R : F →ₗ[ℂ] F), invShiftOperator R hinj γ ⟨w, h⟩ = u := by
  have hsym : ∀ x y : F, inner ℂ (R x) y = inner ℂ x (R y) := by
    intro x y
    have h1 : (ContinuousLinearMap.adjoint R) = R := hR
    rw [← ContinuousLinearMap.adjoint_inner_right, h1]
  have hpre : ∀ x : F, ∀ hx : R x ∈ LinearMap.range (R : F →ₗ[ℂ] F),
      preim R ⟨R x, hx⟩ = x := by
    intro x hx
    apply hinj
    rw [preim_spec]
  set z : F := w - (γ : ℂ) • R w - R u with hz
  have hkey : ∀ x : F, inner ℂ x z = 0 := by
    intro x
    have hx : R x ∈ LinearMap.range (R : F →ₗ[ℂ] F) := ⟨x, rfl⟩
    have h := hw ⟨R x, hx⟩
    have hT : invShiftOperator R hinj γ ⟨R x, hx⟩ = x - (γ : ℂ) • R x := by
      show preim R ⟨R x, hx⟩ - (γ : ℂ) • R x = x - (γ : ℂ) • R x
      rw [hpre]
    rw [hT] at h
    simp only at h
    rw [hz, inner_sub_right, inner_sub_right, inner_smul_right, ← hsym, ← hsym,
      ← h, inner_sub_left, inner_smul_left]
    simp [Complex.conj_ofReal]
  have hz0 : z = 0 := by
    have := hkey z
    exact inner_self_eq_zero.mp this
  have hwR : w = R ((γ : ℂ) • w + u) := by
    rw [map_add, map_smul]
    have : w - (γ : ℂ) • R w - R u = 0 := hz0
    rw [sub_sub, sub_eq_zero] at this
    exact this
  have hmem : w ∈ LinearMap.range (R : F →ₗ[ℂ] F) := ⟨(γ : ℂ) • w + u, hwR.symm⟩
  refine ⟨hmem, ?_⟩
  show preim R ⟨w, hmem⟩ - (γ : ℂ) • w = u
  have hp : preim R ⟨w, hmem⟩ = (γ : ℂ) • w + u := by
    apply hinj
    rw [preim_spec]
    exact hwR
  rw [hp]
  abel

open BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert BookProof.FarisLavine in
theorem P2M_1d5acad2_ext {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (R : F →L[ℂ] F)
    (hinj : Function.Injective R) (γ : ℝ) (hR : IsSelfAdjoint R)
    (hposR : ∀ u : F, γ * ‖R u‖ ^ 2 ≤ (inner ℂ (R u) u : ℂ).re)
    {D : Submodule ℂ F} (hD : D ≤ LinearMap.range (R : F →ₗ[ℂ] F)) (H : D →ₗ[ℂ] F)
    (hH : ∀ x : D, H x = invShiftOperator R hinj γ ⟨(x : F), hD x.2⟩) :
    IsPositiveSelfAdjointExtension H (invShiftOperator R hinj γ) := by
  have hsym : ∀ x y : F, inner ℂ (R x) y = inner ℂ x (R y) := by
    intro x y
    have h1 : (ContinuousLinearMap.adjoint R) = R := hR
    rw [← ContinuousLinearMap.adjoint_inner_right, h1]
  have hT : ∀ y : LinearMap.range (R : F →ₗ[ℂ] F),
      invShiftOperator R hinj γ y = preim R y - (γ : ℂ) • (y : F) := fun y => rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    exact ⟨hD x.2, (hH x).symm⟩
  · intro y z
    rw [hT, hT, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]
    have e1 : (inner ℂ (preim R y) (z : F) : ℂ) = inner ℂ (y : F) (preim R z) := by
      conv_lhs => rw [← preim_spec R z]
      rw [← hsym, preim_spec]
    rw [e1]
    simp [Complex.conj_ofReal]
  · intro y
    show 0 ≤ (inner ℂ (y : F) (invShiftOperator R hinj γ y) : ℂ).re
    rw [hT, inner_sub_right, inner_smul_right]
    have h := hposR (preim R y)
    rw [preim_spec] at h
    have e : (inner ℂ (y : F) (preim R y) : ℂ).re = (inner ℂ (R (preim R y)) (preim R y) : ℂ).re := by
      rw [preim_spec]
    have e2 : (inner ℂ (y : F) (y : F) : ℂ) = ((‖(y : F)‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
    rw [Complex.sub_re, e, e2, ← Complex.ofReal_mul, Complex.ofReal_re]
    rw [preim_spec] at e ⊢
    linarith
  · intro w u hw
    exact P2M_1d5acad2_adj R hinj γ hR w u hw


open BookProof.HermiteGalerkin BookProof.YangMillsFriedrichs BookProof.FriedrichsExtension BookProof.FarisLavine BookProof.HashimotoShiftInvert BookProof.FriedrichsExtension.FormDom Filter Topology in
theorem solution {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (b : HilbertBasis ℕ ℂ F) {n m : ℕ}
    {pi : Fin n → finiteModeDomain b →ₗ[ℂ] finiteModeDomain b}
    {Bf : Fin m → finiteModeDomain b →ₗ[ℂ] finiteModeDomain b}
    (hpi : ∀ i, SymmetricOn (finiteModeDomain b) ((finiteModeDomain b).subtype.comp (pi i)))
    (hB : ∀ a, SymmetricOn (finiteModeDomain b) ((finiteModeDomain b).subtype.comp (Bf a)))
    {γ : ℝ} (hγ : 0 < γ) :
    ∃ (Dom : Submodule ℂ F) (A : Dom →ₗ[ℂ] F) (R : F →L[ℂ] F),
      IsPositiveSelfAdjointExtension (weylOp pi Bf) A ∧ IsShiftInvert A γ R ∧
        IsSelfAdjoint R ∧
        (∀ u : F, Tendsto (fun k : ℕ => galerkinCompression R b k u) atTop (nhds (R u))) ∧
        (∀ (Dom' : Submodule ℂ F) (A' : Dom' →ₗ[ℂ] F), IsShiftInvert A' γ R → Dom' = Dom) := by
  let P : PosSymOp F := ⟨finiteModeDomain b, weylOp pi Bf, weylOpDom_symmetricOn hpi hB,
    weylOpDom_quadForm_nonneg hpi hB⟩
  have hd : P.dom.topologicalClosure = ⊤ := b.dense_span
  have hinj := P2M_1d5acad2_S_inj P hd
  have hD : finiteModeDomain b ≤ LinearMap.range ((friedrichsResolvent P : F →L[ℂ] F) : F →ₗ[ℂ] F) := by
    intro x hx
    exact ⟨x + weylOp pi Bf ⟨x, hx⟩, P2M_1d5acad2_shift P ⟨x, hx⟩⟩
  have hext : IsPositiveSelfAdjointExtension (weylOp pi Bf)
      (invShiftOperator (friedrichsResolvent P) hinj 1) := by
    refine P2M_1d5acad2_ext (friedrichsResolvent P) hinj 1 (P2M_1d5acad2_S_selfadj P)
      (P2M_1d5acad2_S_pos P) hD (weylOp pi Bf) ?_
    intro x
    show weylOp pi Bf x = preim (friedrichsResolvent P) ⟨(x : F), hD x.2⟩ - ((1 : ℝ) : ℂ) • (x : F)
    have hp : preim (friedrichsResolvent P) ⟨(x : F), hD x.2⟩ = (x : F) + weylOp pi Bf x := by
      apply hinj
      rw [preim_spec]
      exact (P2M_1d5acad2_shift P x).symm
    rw [hp, Complex.ofReal_one, one_smul]
    abel
  have hext' := hext
  obtain ⟨-, hsym, hpos, hsa⟩ := hext'
  have hsurj := P2M_1d5acad2_surj hsym hpos hsa hγ
  obtain ⟨R, hR⟩ := P2M_1d5acad2_exists hpos hγ hsurj
  have hRsa : IsSelfAdjoint R := P2M_1d5acad2_selfadj hR hsym
  exact ⟨_, _, R, hext, hR, hRsa, fun u => P2M_1d5acad2_comp_tendsto R b u,
    fun Dom' A' h' => (P2M_1d5acad2_determines h' hR).1⟩
