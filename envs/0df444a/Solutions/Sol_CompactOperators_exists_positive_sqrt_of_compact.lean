-- Prove2me | solution 1 for CompactOperators.exists_positive_sqrt_of_compact
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T22:20:50.736343+00:00
-- url     : https://prove2.me/submissions/e3274b07-44f3-4f67-a811-aca5a3e275be

import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Lp.lpHolder
open scoped InnerProductSpace
open Module.End
universe u v
set_option maxHeartbeats 800000
namespace CompactSpectral
variable {𝕜 : Type v} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
noncomputable def get_basis (T : E →L[𝕜] E) (μ : 𝕜) :
    Σ (w : Set (Module.End.eigenspace (T : Module.End 𝕜 E) μ)),
      HilbertBasis w 𝕜 (Module.End.eigenspace (T : Module.End 𝕜 E) μ) := by
  haveI : CompleteSpace (Module.End.eigenspace (T : Module.End 𝕜 E) μ) :=
    IsClosed.completeSpace_coe (hs := ContinuousLinearMap.isClosed_eigenspace T μ)
  have h := exists_hilbertBasis 𝕜 (Module.End.eigenspace (T : Module.End 𝕜 E) μ)
  exact ⟨Classical.choose h, Classical.choose (Classical.choose_spec h)⟩
noncomputable def v' (T : E →L[𝕜] E) (p : Σ (μ : 𝕜), (get_basis T μ).1) : E :=
  ((get_basis T p.1).2 p.2 : E)
lemma v'_orthonormal (T : E →L[𝕜] E) (hsym : (T : E →ₗ[𝕜] E).IsSymmetric) :
    Orthonormal 𝕜 (v' T) :=
  OrthogonalFamily.orthonormal_sigma_orthonormal
    (LinearMap.IsSymmetric.orthogonalFamily_eigenspaces hsym)
    (fun μ => (get_basis T μ).2.orthonormal)
lemma v'_eigenvector (T : E →L[𝕜] E) (p : Σ (μ : 𝕜), (get_basis T μ).1) :
    T (v' T p) = p.1 • v' T p :=
  Module.End.mem_eigenspace_iff.mp ((get_basis T p.1).2 p.2).2
lemma orthogonal_eigenspace (T : E →L[𝕜] E) (x : E)
    (hx : x ∈ (Submodule.span 𝕜 (Set.range (v' T)))ᗮ) (μ : 𝕜) :
    x ∈ (Module.End.eigenspace (T : Module.End 𝕜 E) μ)ᗮ := by
  let W := Module.End.eigenspace (T : Module.End 𝕜 E) μ
  rw [Submodule.mem_orthogonal']
  intro y hy
  let y_W : W := ⟨y, hy⟩
  let b := (get_basis T μ).2
  have hsum := ((b.hasSum_repr y_W).mapL W.subtypeL).mapL (innerSL 𝕜 x)
  have hzero (i : (get_basis T μ).1) : ⟪x, W.subtype (b i)⟫_𝕜 = 0 := by
    have h_mem : W.subtype (b i) ∈ Submodule.span 𝕜 (Set.range (v' T)) :=
      Submodule.subset_span ⟨⟨μ, i⟩, rfl⟩
    exact Submodule.inner_left_of_mem_orthogonal h_mem hx
  have hzero' (i : (get_basis T μ).1) :
      (innerSL 𝕜 x) (W.subtypeL (b.repr y_W i • b i)) = 0 := by
    rw [map_smul, Submodule.coe_subtypeL, innerSL_apply_apply, inner_smul_right, hzero, mul_zero]
  simp only [hzero'] at hsum
  have h_inner : ⟪x, y⟫_𝕜 = 0 := hsum.unique hasSum_zero
  exact h_inner
lemma orthogonalComplement_span_range_v'_eq_bot (T : E →L[𝕜] E)
    (hT : IsCompactOperator T) (hsym : (T : E →ₗ[𝕜] E).IsSymmetric) :
    (Submodule.span 𝕜 (Set.range (v' T)))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  have h_orth (μ : 𝕜) : x ∈ (Module.End.eigenspace (T : Module.End 𝕜 E) μ)ᗮ :=
    orthogonal_eigenspace T x hx μ
  have h_iInf : x ∈ ⨅ μ, (Module.End.eigenspace (T : Module.End 𝕜 E) μ)ᗮ := by
    rw [Submodule.mem_iInf]
    exact h_orth
  rw [Submodule.iInf_orthogonal] at h_iInf
  have h_bot : (⨆ μ, Module.End.eigenspace (T : Module.End 𝕜 E) μ)ᗮ = ⊥ :=
    ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hT hsym
  rw [h_bot, Submodule.mem_bot] at h_iInf
  exact h_iInf
 theorem eigenbasis_set (T : E →L[𝕜] E) (hT : IsCompactOperator T)
    (hsym : (T : E →ₗ[𝕜] E).IsSymmetric) :
    ∃ (s : Set E) (b : HilbertBasis s 𝕜 E) (μ : s → 𝕜),
      ∀ j, T (b j) = μ j • b j := by
  let s := Set.range (v' T)
  have hv' : Orthonormal 𝕜 (v' T) := v'_orthonormal T hsym
  let e : s ≃ (Σ (μ : 𝕜), (get_basis T μ).1) :=
    (Equiv.ofInjective (v' T) hv'.linearIndependent.injective).symm
  let v : s → E := v' T ∘ e
  have hv : Orthonormal 𝕜 v := hv'.comp e e.injective
  have h_range : Set.range v = Set.range (v' T) := e.surjective.range_comp (v' T)
  have hbot : (Submodule.span 𝕜 (Set.range v))ᗮ = ⊥ := by
    rw [h_range]
    exact orthogonalComplement_span_range_v'_eq_bot T hT hsym
  let b : HilbertBasis s 𝕜 E := HilbertBasis.mkOfOrthogonalEqBot hv hbot
  have hb : (b : s → E) = v := HilbertBasis.coe_mkOfOrthogonalEqBot hv hbot
  refine ⟨s, b, fun j ↦ (e j).1, fun j ↦ ?_⟩
  change T (b j) = (e j).1 • b j
  rw [congr_fun hb j]
  exact v'_eigenvector T (e j)
theorem eigenbasis_set_real (T : E →L[𝕜] E) (hT : IsCompactOperator T)
    (hsym : (T : E →ₗ[𝕜] E).IsSymmetric) :
    ∃ (s : Set E) (b : HilbertBasis s 𝕜 E) (μ : s → ℝ),
      ∀ j, T (b j) = (μ j : 𝕜) • b j := by
  obtain ⟨s, b, μ, hμ⟩ := eigenbasis_set T hT hsym
  refine ⟨s, b, fun j ↦ RCLike.re (μ j), fun j ↦ ?_⟩
  have heig : HasEigenvalue (T : Module.End 𝕜 E) (μ j) :=
    hasEigenvalue_of_hasEigenvector ⟨mem_eigenspace_iff.mpr (hμ j), b.orthonormal.ne_zero j⟩
  have hreal : ((RCLike.re (μ j) : ℝ) : 𝕜) = μ j :=
    RCLike.conj_eq_iff_re.mp (hsym.conj_eigenvalue_eq_self heig)
  rw [hreal]
  exact hμ j
end CompactSpectral

theorem diagonal {𝕜 : Type v} [RCLike 𝕜] {ι : Type u}
    (d : ι → ℝ) (K : ℝ) (hK : 0 ≤ K) (hd₀ : ∀ i, 0 ≤ d i) (hdK : ∀ i, d i ≤ K) :
    ∃ D : lp (fun _ : ι => 𝕜) 2 →L[𝕜] lp (fun _ : ι => 𝕜) 2,
      D.IsPositive ∧ ∀ x i, D x i = (d i : 𝕜) * x i := by
  classical
  let S : lp (fun _ : ι => 𝕜) 2 →L[𝕜] lp (fun _ : ι => 𝕜) 2 :=
    lp.mapCLM 2 (fun i => ContinuousLinearMap.lsmul 𝕜 𝕜 ((Real.sqrt (d i) : ℝ) : 𝕜))
      (Real.sqrt_nonneg K) (fun i => by
        calc
          _ ≤ ‖((Real.sqrt (d i) : ℝ) : 𝕜)‖ := ContinuousLinearMap.opNorm_lsmul_apply_le _
          _ = Real.sqrt (d i) := by simp [Real.sqrt_nonneg]
          _ ≤ Real.sqrt K := Real.sqrt_le_sqrt (hdK i))
  have hS (x : lp (fun _ : ι => 𝕜) 2) (i : ι) :
      S x i = (Real.sqrt (d i) : 𝕜) * x i := by simp [S]
  have hsingle (i : ι) : S (lp.single 2 i (1 : 𝕜)) =
      Real.sqrt (d i) • lp.single 2 i (1 : 𝕜) := by
    ext j
    by_cases h : j = i
    · subst j; simp [hS, RCLike.real_smul_eq_coe_mul]
    · simp [hS, lp.single_apply, h]
  refine ⟨S.adjoint.comp S, ContinuousLinearMap.isPositive_adjoint_comp_self S, ?_⟩
  intro x i
  have hh := ContinuousLinearMap.adjoint_inner_right S (lp.single 2 i (1 : 𝕜)) (S x)
  rw [hsingle, RCLike.real_smul_eq_coe_smul (K := 𝕜), inner_smul_left,
    lp.inner_single_left, lp.inner_single_left] at hh
  simp only [RCLike.inner_apply, map_one, one_mul, hS, RCLike.conj_ofReal] at hh
  have hs : (Real.sqrt (d i) : 𝕜) * (Real.sqrt (d i) : 𝕜) = (d i : 𝕜) := by
    rw [← RCLike.ofReal_mul, Real.mul_self_sqrt (hd₀ i)]
  simpa [ContinuousLinearMap.comp_apply, ← mul_assoc, hs] using hh

theorem solution {𝕜 : Type v} [RCLike 𝕜]
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (A : E →L[𝕜] E) (hA : IsCompactOperator A) (hp : A.IsPositive) :
    ∃ B : E →L[𝕜] E, B.IsPositive ∧ B.comp B = A := by
  classical
  obtain ⟨s, b, μ, hμ⟩ := CompactSpectral.eigenbasis_set_real A hA hp.isSymmetric
  have hnorm (i : s) : ‖b i‖ = 1 := b.orthonormal.norm_eq_one i
  have hnonneg (i : s) : 0 ≤ μ i := by
    have h := hp.re_inner_nonneg_left (b i)
    rw [hμ i, inner_smul_left] at h
    simpa [inner_self_eq_norm_sq, hnorm i] using h
  have hbound (i : s) : μ i ≤ ‖A‖ := by
    have h := A.le_opNorm (b i)
    rw [hμ i, norm_smul, hnorm i] at h
    simpa [Real.norm_eq_abs, abs_of_nonneg (hnonneg i)] using h
  obtain ⟨D, hD, hDcoord⟩ := diagonal (𝕜 := 𝕜) (fun i : s => Real.sqrt (μ i)) (Real.sqrt ‖A‖)
    (Real.sqrt_nonneg _) (fun i => Real.sqrt_nonneg _) (fun i => Real.sqrt_le_sqrt (hbound i))
  let U := b.repr
  let B : E →L[𝕜] E := (U.symm : lp (fun _ : s => 𝕜) 2 →L[𝕜] E).comp (D.comp (U : E →L[𝕜] _))
  refine ⟨B, ?_, ?_⟩
  · simpa [B, U, LinearIsometryEquiv.adjoint_eq_symm] using hD.adjoint_conj (b.repr : E →L[𝕜] _)
  · ext x
    apply U.injective
    ext i
    have hcoord : U (A x) i = (μ i : 𝕜) * U x i := by
      change b.repr (A x) i = (μ i : 𝕜) * b.repr x i
      rw [b.repr_apply_apply, b.repr_apply_apply]
      calc
        ⟪b i, A x⟫_𝕜 = ⟪A (b i), x⟫_𝕜 := (hp.inner_left_eq_inner_right (b i) x).symm
        _ = (μ i : 𝕜) * ⟪b i, x⟫_𝕜 := by rw [hμ i, inner_smul_left, RCLike.conj_ofReal]
    change U (U.symm (D (U (U.symm (D (U x)))))) i = U (A x) i
    simp only [U.apply_symm_apply]
    rw [hDcoord, hDcoord, hcoord, ← mul_assoc, ← RCLike.ofReal_mul, Real.mul_self_sqrt (hnonneg i)]
