-- Prove2me | solution 1 for BookProof.HashimotoShiftInvert.hashimoto_shiftInvert_unbounded_example
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T18:02:16.915976+00:00
-- url     : https://prove2.me/submissions/2bfc7c15-5d92-4503-a0c7-3020b9c63181

import Mathlib
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterComplexShiftCore

set_option autoImplicit false

open BookProof.HashimotoShiftInvert BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit BookProof.HermiteGalerkin Filter Topology in
theorem P2M_21b6ab40_determines {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
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
theorem P2M_21b6ab40_proj_tendsto {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
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
theorem P2M_21b6ab40_comp_tendsto {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (T : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F) (u : F) :
    Tendsto (fun m : ℕ => galerkinCompression T b m u) atTop (𝓝 (T u)) := by
  have h1 : Tendsto (fun m : ℕ => T ((galerkinSpan b m).starProjection u)) atTop (𝓝 (T u)) :=
    (T.continuous.tendsto u).comp (P2M_21b6ab40_proj_tendsto b u)
  have h2 := P2M_21b6ab40_proj_tendsto b (T u)
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
theorem P2M_21b6ab40_lower {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
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
theorem P2M_21b6ab40_apply_resolvent {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
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
theorem P2M_21b6ab40_resolvent_tendsto {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {R : F →L[ℂ] F} (hR : IsSelfAdjoint R) (T : ℕ → F →L[ℂ] F) (hT : ∀ m, IsSelfAdjoint (T m))
    (hconv : ∀ v : F, Tendsto (fun m => T m v) atTop (𝓝 (R v)))
    {z : ℂ} (hz : z.im ≠ 0) (u : F) :
    Tendsto (fun m => resolvent (T m) z u) atTop (𝓝 (resolvent R z u)) := by
  set y := resolvent R z u with hy
  have hpos : 0 < |z.im| := abs_pos.mpr hz
  have key : ∀ m, ‖resolvent (T m) z u - y‖ ≤ ‖T m y - R y‖ / |z.im| := by
    intro m
    rw [le_div_iff₀ hpos, mul_comm]
    have hl := P2M_21b6ab40_lower (hT m) z (resolvent (T m) z u - y)
    have heq : (algebraMap ℂ (F →L[ℂ] F) z - T m) (resolvent (T m) z u - y) = T m y - R y := by
      rw [map_sub, P2M_21b6ab40_apply_resolvent (hT m) hz u]
      conv_lhs => rw [← P2M_21b6ab40_apply_resolvent hR hz u]
      simp only [ContinuousLinearMap.sub_apply]
      abel
    rw [heq] at hl
    exact hl
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h0 : Tendsto (fun m => ‖T m y - R y‖ / |z.im|) atTop (𝓝 0) := by
    have := ((tendsto_iff_norm_sub_tendsto_zero.mp (hconv y)).div_const |z.im|)
    simpa using this

  exact squeeze_zero (fun _ => norm_nonneg _) key h0

open scoped lp in
open BookProof.HashimotoShiftInvert BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit BookProof.HermiteGalerkin Filter Topology in
theorem P2M_21b6ab40_shift (x : LinearMap.range (ell2ShiftInvert : ℓ²(ℕ, ℂ) →ₗ[ℂ] ℓ²(ℕ, ℂ))) :
    shiftMap ell2UnboundedExample 1 x = preim ell2ShiftInvert x := by
  show (preim ell2ShiftInvert x - ((1:ℝ):ℂ) • (x : ℓ²(ℕ, ℂ))) + ((1:ℝ):ℂ) • (x : ℓ²(ℕ, ℂ)) = _
  rw [sub_add_cancel]

open scoped lp in
open BookProof.HashimotoShiftInvert BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit BookProof.HermiteGalerkin Filter Topology in
theorem P2M_21b6ab40_isSI : IsShiftInvert ell2UnboundedExample 1 ell2ShiftInvert := by
  refine ⟨fun x => ?_, fun u => ⟨LinearMap.mem_range_self (ell2ShiftInvert : ℓ²(ℕ, ℂ) →ₗ[ℂ] ℓ²(ℕ, ℂ)) u, ?_⟩⟩
  · rw [P2M_21b6ab40_shift]; exact preim_spec _ _
  · rw [P2M_21b6ab40_shift]; apply ell2ShiftInvert_injective; exact preim_spec _ _

open scoped lp in
open BookProof.HashimotoShiftInvert BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit BookProof.HermiteGalerkin Filter Topology in
theorem P2M_21b6ab40_norm : ‖ell2ShiftInvert‖ ≤ 1 := by
  unfold ell2ShiftInvert diagCLM
  exact LinearMap.mkContinuous_norm_le _ zero_le_one _

open scoped lp in
open BookProof.HashimotoShiftInvert BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit BookProof.HermiteGalerkin Filter Topology in
theorem P2M_21b6ab40_sa : IsSelfAdjoint ell2ShiftInvert := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  simp only [ContinuousLinearMap.coe_coe]
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr (fun n => ?_)
  rw [ell2ShiftInvert, diagCLM_apply, diagCLM_apply]
  simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

open scoped lp in
open BookProof.HashimotoShiftInvert BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit BookProof.HermiteGalerkin Filter Topology in
theorem P2M_21b6ab40_unb (C : ℝ) : ∃ x : finiteModeDomain ell2Basis,
      C * ‖(x : ℓ²(ℕ, ℂ))‖ < ‖ell2ExampleMatrix x‖ := by
  obtain ⟨k, hk⟩ := exists_nat_gt C
  refine ⟨⟨ell2Basis k, Submodule.subset_span ⟨k, rfl⟩⟩, ?_⟩
  have hnorm : ‖(ell2Basis k : ℓ²(ℕ, ℂ))‖ = 1 := ell2Basis.orthonormal.1 k
  have hpre : preim ell2ShiftInvert ⟨ell2Basis k, ell2Basis_mem_range k⟩
      = ((k:ℂ) + 1) • (ell2Basis k : ℓ²(ℕ, ℂ)) := by
    apply ell2ShiftInvert_injective
    rw [preim_spec]
    show (ell2Basis k : ℓ²(ℕ, ℂ)) = _
    rw [ell2Basis_apply, ell2ShiftInvert_smul_single]
  have hval : ell2ExampleMatrix ⟨ell2Basis k, Submodule.subset_span ⟨k, rfl⟩⟩
      = (k : ℂ) • (ell2Basis k : ℓ²(ℕ, ℂ)) := by
    show preim ell2ShiftInvert ⟨ell2Basis k, ell2Basis_mem_range k⟩
      - ((1:ℝ):ℂ) • (ell2Basis k : ℓ²(ℕ, ℂ)) = _
    rw [hpre, add_smul, Complex.ofReal_one, one_smul, add_sub_cancel_right]
  rw [hval, norm_smul, hnorm, Complex.norm_natCast]
  linarith

open scoped lp in open BookProof.HashimotoShiftInvert BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit BookProof.HermiteGalerkin Filter Topology in
theorem solution :
    IsShiftInvert ell2UnboundedExample 1 ell2ShiftInvert ∧
    ‖ell2ShiftInvert‖ ≤ 1 ∧ IsSelfAdjoint ell2ShiftInvert ∧
    (∀ u : ℓ²(ℕ, ℂ), Tendsto
      (fun m : ℕ => galerkinCompression ell2ShiftInvert ell2Basis m u) atTop
        (nhds (ell2ShiftInvert u))) ∧
    (∀ z : ℂ, z.im ≠ 0 → ∀ u : ℓ²(ℕ, ℂ), Tendsto
      (fun m : ℕ => resolvent (galerkinCompression ell2ShiftInvert ell2Basis m) z u) atTop
        (nhds (resolvent ell2ShiftInvert z u))) ∧
    (∀ (Dom' : Submodule ℂ (ℓ²(ℕ, ℂ))) (A' : Dom' →ₗ[ℂ] ℓ²(ℕ, ℂ)),
      IsShiftInvert A' 1 ell2ShiftInvert →
      Dom' = LinearMap.range (ell2ShiftInvert : ℓ²(ℕ, ℂ) →ₗ[ℂ] ℓ²(ℕ, ℂ))) ∧
    (∀ C : ℝ, ∃ x : finiteModeDomain ell2Basis,
      C * ‖(x : ℓ²(ℕ, ℂ))‖ < ‖ell2ExampleMatrix x‖) := by
  have hRsa := P2M_21b6ab40_sa
  refine ⟨P2M_21b6ab40_isSI, P2M_21b6ab40_norm, hRsa,
    fun u => P2M_21b6ab40_comp_tendsto ell2ShiftInvert ell2Basis u, ?_, ?_, P2M_21b6ab40_unb⟩
  · intro z hz u
    exact P2M_21b6ab40_resolvent_tendsto hRsa (fun m => galerkinCompression ell2ShiftInvert ell2Basis m)
      (fun m => hRsa.conj_starProjection (galerkinSpan ell2Basis m))
      (fun v => P2M_21b6ab40_comp_tendsto ell2ShiftInvert ell2Basis v) hz u
  · intro Dom' A' h
    exact (P2M_21b6ab40_determines h P2M_21b6ab40_isSI).1
