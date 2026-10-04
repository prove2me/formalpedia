-- Prove2me | solution 2 for BookProof.HashimotoShiftInvert.hashimoto_shiftInvert_selects_friedrichs
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T03:44:03.419064+00:00
-- url     : https://prove2.me/submissions/f8864a7f-2ae8-4ace-99b3-e0f86abd2f14

import Mathlib
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichsLimit
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterComplexShiftCore

set_option autoImplicit false





open BookProof.HashimotoShiftInvert BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit BookProof.HermiteGalerkin Filter Topology in
theorem P2M_2e4f603a_shift_ge {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
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

open BookProof.HashimotoShiftInvert BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit BookProof.HermiteGalerkin Filter Topology in
theorem P2M_2e4f603a_closed {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
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
      P2M_2e4f603a_shift_ge hpos hγ _
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


open BookProof.HashimotoShiftInvert BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit BookProof.HermiteGalerkin Filter Topology in
theorem P2M_2e4f603a_orth {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
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

open BookProof.HashimotoShiftInvert BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit BookProof.HermiteGalerkin Filter Topology in
theorem P2M_2e4f603a_surj {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {Dom : Submodule ℂ F} {A : Dom →ₗ[ℂ] F} (hsym : SymmetricOn Dom A)
    (hpos : ∀ x : Dom, 0 ≤ quadForm A x)
    (hsa : ∀ w u : F, (∀ v : Dom, (inner ℂ (A v) w : ℂ) = inner ℂ (v : F) u) →
      ∃ h : w ∈ Dom, A ⟨w, h⟩ = u)
    {γ : ℝ} (hγ : 0 < γ) : Function.Surjective (shiftMap A γ) := by
  have hclosed : IsClosed ((shiftRange A γ : Submodule ℂ F) : Set F) :=
    P2M_2e4f603a_closed hsym hpos hsa hγ
  haveI : CompleteSpace (shiftRange A γ) := hclosed.completeSpace_coe
  have htop : shiftRange A γ = ⊤ := by
    have h1 := Submodule.orthogonal_orthogonal (shiftRange A γ)
    rw [P2M_2e4f603a_orth hpos hsa hγ, Submodule.bot_orthogonal_eq_top] at h1
    exact h1.symm
  intro u
  have hmem : u ∈ shiftRange A γ := by rw [htop]; trivial
  exact hmem


open BookProof.HashimotoShiftInvert BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit BookProof.HermiteGalerkin Filter Topology in
theorem P2M_2e4f603a_exists {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {Dom : Submodule ℂ F} {A : Dom →ₗ[ℂ] F} (hpos : ∀ x : Dom, 0 ≤ quadForm A x)
    {γ : ℝ} (hγ : 0 < γ) (hsurj : Function.Surjective (shiftMap A γ)) :
    ∃ R : F →L[ℂ] F, IsShiftInvert A γ R := by
  have hinj : Function.Injective (shiftMap A γ) := by
    intro x y hxy
    have h := P2M_2e4f603a_shift_ge hpos hγ (x - y)
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
    have h := P2M_2e4f603a_shift_ge hpos hγ (f.symm u)
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

open BookProof.HashimotoShiftInvert BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit BookProof.HermiteGalerkin Filter Topology in
theorem P2M_2e4f603a_selfadj {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
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

open BookProof.HashimotoShiftInvert BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit BookProof.HermiteGalerkin Filter Topology in
theorem P2M_2e4f603a_nonneg {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {Dom : Submodule ℂ F} {A : Dom →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F}
    (h : IsShiftInvert A γ R) (hpos : ∀ x : Dom, 0 ≤ quadForm A x) (hγ : 0 < γ) (u : F) :
    0 ≤ (inner ℂ u (R u) : ℂ).re := by
  obtain ⟨hR, hu⟩ := h.2 u
  set x : Dom := ⟨R u, hR⟩ with hx
  have hxu : (x : F) = R u := rfl
  have key : A x + ((γ : ℂ) • (x : F)) = u := by
    rw [← hu]; simp [shiftMap, x]
  rw [← hxu]
  conv_rhs => rw [← key]
  rw [inner_add_left, Complex.add_re, inner_smul_left]
  have h1 : (inner ℂ (A x) (x : F) : ℂ).re = quadForm A x := by
    unfold quadForm
    rw [← inner_conj_symm, Complex.conj_re]
  have h2 : ((starRingEnd ℂ) (γ : ℂ) * inner ℂ (x : F) (x : F)).re = γ * ‖(x : F)‖ ^ 2 := by
    rw [Complex.conj_ofReal, inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  rw [h1, h2]
  have := hpos x
  positivity

open BookProof.HashimotoShiftInvert BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit BookProof.HermiteGalerkin Filter Topology in
theorem P2M_2e4f603a_opnorm {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {Dom : Submodule ℂ F} {A : Dom →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F}
    (h : IsShiftInvert A γ R) (hpos : ∀ x : Dom, 0 ≤ quadForm A x) (hγ : 0 < γ) :
    ‖R‖ ≤ γ⁻¹ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.2 hγ.le) ?_
  intro u
  obtain ⟨hm, hu⟩ := h.2 u
  set x : Dom := ⟨R u, hm⟩ with hxdef
  have hxF : (x : F) = R u := rfl
  have hsm : shiftMap A γ x = A x + (γ : ℂ) • (x : F) := by
    simp [shiftMap]
  have hkey : RCLike.re (inner ℂ (x : F) u) = quadForm A x + γ * ‖(x : F)‖ ^ 2 := by
    rw [← hu, hsm, inner_add_right, inner_smul_right, map_add]
    have h1 : RCLike.re ((γ : ℂ) * inner ℂ (x : F) (x : F)) = γ * ‖(x : F)‖ ^ 2 := by
      show ((γ : ℂ) * inner ℂ (x : F) (x : F)).re = _
      rw [Complex.re_ofReal_mul]
      congr 1
      exact inner_self_eq_norm_sq (𝕜 := ℂ) (x : F)
    rw [h1]
    rfl
  have hle : RCLike.re (inner ℂ (x : F) u) ≤ ‖(x : F)‖ * ‖u‖ := re_inner_le_norm _ _
  have hq := hpos x
  rw [← hxF]
  have hmain : γ * ‖(x : F)‖ ^ 2 ≤ ‖(x : F)‖ * ‖u‖ := by linarith
  rcases eq_or_lt_of_le (norm_nonneg (x : F)) with h0 | h0
  · rw [← h0]; positivity
  · have : γ * ‖(x : F)‖ ≤ ‖u‖ := by
      have := hmain
      nlinarith
    rw [inv_mul_eq_div, le_div_iff₀ hγ]
    linarith

open BookProof.HashimotoShiftInvert BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit BookProof.HermiteGalerkin Filter Topology in
theorem P2M_2e4f603a_determines {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
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

open BookProof.HashimotoShiftInvert BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit BookProof.HermiteGalerkin Filter Topology in
theorem P2M_2e4f603a_proj_tendsto {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
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

open BookProof.HashimotoShiftInvert BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit BookProof.HermiteGalerkin Filter Topology in
theorem P2M_2e4f603a_comp_tendsto {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (T : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F) (u : F) :
    Tendsto (fun m : ℕ => galerkinCompression T b m u) atTop (𝓝 (T u)) := by
  have h1 : Tendsto (fun m : ℕ => T ((galerkinSpan b m).starProjection u)) atTop (𝓝 (T u)) :=
    (T.continuous.tendsto u).comp (P2M_2e4f603a_proj_tendsto b u)
  have h2 := P2M_2e4f603a_proj_tendsto b (T u)
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

open BookProof.HashimotoShiftInvert BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit BookProof.HermiteGalerkin Filter Topology in
theorem P2M_2e4f603a_lower {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {S : F →L[ℂ] F} (hS : IsSelfAdjoint S) (z : ℂ) (x : F) :
    |z.im| * ‖x‖ ≤ ‖(algebraMap ℂ (F →L[ℂ] F) z - S) x‖ := by
  have happ : (algebraMap ℂ (F →L[ℂ] F) z - S) x = z • x - S x := by
    simp [Algebra.algebraMap_eq_smul_one]
  have hsymm : (inner ℂ (S x) x : ℂ) = inner ℂ x (S x) :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hS) x x
  have hreal : (inner ℂ x (S x) : ℂ).im = 0 := by
    have hc : (starRingEnd ℂ) (inner ℂ x (S x) : ℂ) = inner ℂ x (S x) := by
      rw [inner_conj_symm, hsymm]
    exact Complex.conj_eq_iff_im.mp hc
  have him : (inner ℂ x ((algebraMap ℂ (F →L[ℂ] F) z - S) x) : ℂ).im = z.im * ‖x‖ ^ 2 := by
    rw [happ, inner_sub_right, inner_smul_right, Complex.sub_im, Complex.mul_im,
      inner_self_eq_norm_sq_to_K, hreal]
    simp [← Complex.ofReal_pow]
  have h2 : |(inner ℂ x ((algebraMap ℂ (F →L[ℂ] F) z - S) x) : ℂ).im| ≤
      ‖x‖ * ‖(algebraMap ℂ (F →L[ℂ] F) z - S) x‖ :=
    le_trans (Complex.abs_im_le_norm _) (norm_inner_le_norm _ _)
  rw [him, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖x‖ ^ 2)] at h2
  rcases eq_or_lt_of_le (norm_nonneg x) with h0 | hpx
  · rw [← h0]; simp
  · nlinarith [abs_nonneg z.im]

open BookProof.HashimotoShiftInvert BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit BookProof.HermiteGalerkin Filter Topology in
theorem P2M_2e4f603a_apply_resolvent {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {S : F →L[ℂ] F} (hS : IsSelfAdjoint S) {z : ℂ} (hz : z.im ≠ 0) (u : F) :
    (algebraMap ℂ (F →L[ℂ] F) z - S) (resolvent S z u) = u := by
  have hnot : z ∉ spectrum ℂ S := by
    intro hmem
    have h := hS.mem_spectrum_eq_re hmem
    apply hz
    rw [h]
    simp
  have hunit : IsUnit (algebraMap ℂ (F →L[ℂ] F) z - S) := spectrum.notMem_iff.mp hnot
  have h1 := Ring.mul_inverse_cancel _ hunit
  have h2 := congrArg (fun T : F →L[ℂ] F => T u) h1
  simpa [resolvent] using h2

open BookProof.HashimotoShiftInvert BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit BookProof.HermiteGalerkin Filter Topology in
theorem P2M_2e4f603a_resolvent_tendsto {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {R : F →L[ℂ] F} (hR : IsSelfAdjoint R) (T : ℕ → F →L[ℂ] F) (hT : ∀ m, IsSelfAdjoint (T m))
    (hconv : ∀ v : F, Tendsto (fun m => T m v) atTop (𝓝 (R v)))
    {z : ℂ} (hz : z.im ≠ 0) (u : F) :
    Tendsto (fun m => resolvent (T m) z u) atTop (𝓝 (resolvent R z u)) := by
  set y := resolvent R z u with hy
  have hpos : 0 < |z.im| := abs_pos.mpr hz
  have key : ∀ m, ‖resolvent (T m) z u - y‖ ≤ ‖T m y - R y‖ / |z.im| := by
    intro m
    rw [le_div_iff₀ hpos, mul_comm]
    have hl := P2M_2e4f603a_lower (hT m) z (resolvent (T m) z u - y)
    have heq : (algebraMap ℂ (F →L[ℂ] F) z - T m) (resolvent (T m) z u - y) = T m y - R y := by
      rw [map_sub, P2M_2e4f603a_apply_resolvent (hT m) hz u]
      conv_lhs => rw [← P2M_2e4f603a_apply_resolvent hR hz u]
      simp only [ContinuousLinearMap.sub_apply]
      abel
    rw [heq] at hl
    exact hl
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h0 : Tendsto (fun m => ‖T m y - R y‖ / |z.im|) atTop (𝓝 0) := by
    have := ((tendsto_iff_norm_sub_tendsto_zero.mp (hconv y)).div_const |z.im|)
    simpa using this

  exact squeeze_zero (fun _ => norm_nonneg _) key h0

open BookProof.HashimotoShiftInvert BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit BookProof.HermiteGalerkin Filter Topology in
theorem solution {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (b : HilbertBasis ℕ ℂ F)
    (H : finiteModeDomain b →ₗ[ℂ] F) {Dom : Submodule ℂ F} (A : Dom →ₗ[ℂ] F)
    (hA : IsPositiveSelfAdjointExtension H A) {γ : ℝ} (hγ : 0 < γ) :
    ∃ R : F →L[ℂ] F,
      IsShiftInvert A γ R ∧ ‖R‖ ≤ γ⁻¹ ∧ IsSelfAdjoint R ∧
      (∀ u : F, 0 ≤ (inner ℂ u (R u) : ℂ).re) ∧
      (∀ u : F, Tendsto (fun m : ℕ => galerkinCompression R b m u) atTop (nhds (R u))) ∧
      (∀ z : ℂ, z.im ≠ 0 → ∀ u : F,
        Tendsto (fun m : ℕ => resolvent (galerkinCompression R b m) z u) atTop
          (nhds (resolvent R z u))) ∧
      (∀ (Dom' : Submodule ℂ F) (A' : Dom' →ₗ[ℂ] F), IsShiftInvert A' γ R →
        Dom' = Dom ∧ ∀ (x : F) (hx : x ∈ Dom) (hx' : x ∈ Dom'), A' ⟨x, hx'⟩ = A ⟨x, hx⟩) := by
  obtain ⟨-, hsym, hpos, hsa⟩ := hA
  have hsurj := P2M_2e4f603a_surj hsym hpos hsa hγ
  obtain ⟨R, hR⟩ := P2M_2e4f603a_exists hpos hγ hsurj
  have hRsa : IsSelfAdjoint R := P2M_2e4f603a_selfadj hR hsym
  refine ⟨R, hR, P2M_2e4f603a_opnorm hR hpos hγ, hRsa, P2M_2e4f603a_nonneg hR hpos hγ,
    fun u => P2M_2e4f603a_comp_tendsto R b u, ?_, ?_⟩
  · intro z hz u
    exact P2M_2e4f603a_resolvent_tendsto hRsa (fun m => galerkinCompression R b m)
      (fun m => hRsa.conj_starProjection (galerkinSpan b m))
      (fun v => P2M_2e4f603a_comp_tendsto R b v) hz u
  · intro Dom' A' h'
    obtain ⟨hD, hE⟩ := P2M_2e4f603a_determines h' hR
    exact ⟨hD, fun x hx hx' => hE x hx' hx⟩
