-- Prove2me | solution 1 for CompactOperators.exists_hilbertBasis_of_compact_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T19:35:08.905843+00:00
-- url     : https://prove2.me/submissions/5b93b287-52d3-4789-8d7f-fa5ef527a642

import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Operator.Compact.Basic

open scoped InnerProductSpace
open Module.End

universe u v

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

theorem eigenbasis (T : E →L[𝕜] E) (hT : IsCompactOperator T)
    (hsym : (T : E →ₗ[𝕜] E).IsSymmetric) :
    ∃ (ι : Type (max u v)) (b : HilbertBasis ι 𝕜 E) (μ : ι → 𝕜),
      ∀ j, T (b j) = μ j • b j := by
  let ι := Σ (μ : 𝕜), (get_basis T μ).1
  have hv : Orthonormal 𝕜 (v' T) := v'_orthonormal T hsym
  have hbot : (Submodule.span 𝕜 (Set.range (v' T)))ᗮ = ⊥ :=
    orthogonalComplement_span_range_v'_eq_bot T hT hsym
  let b : HilbertBasis ι 𝕜 E := HilbertBasis.mkOfOrthogonalEqBot hv hbot
  have hb : (b : ι → E) = v' T := HilbertBasis.coe_mkOfOrthogonalEqBot hv hbot
  refine ⟨ι, b, fun j ↦ j.1, fun j ↦ ?_⟩
  rw [congr_fun hb j]
  exact v'_eigenvector T j

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


theorem solution {𝕜 : Type v} [RCLike 𝕜] {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] (T : E →L[𝕜] E)
    (hT : IsCompactOperator T) (hsym : (T : E →ₗ[𝕜] E).IsSymmetric) :
    ∃ (s : Set E) (b : HilbertBasis s 𝕜 E) (μ : s → ℝ),
      ∀ j, T (b j) = (μ j : 𝕜) • b j :=
  CompactSpectral.eigenbasis_set_real T hT hsym
