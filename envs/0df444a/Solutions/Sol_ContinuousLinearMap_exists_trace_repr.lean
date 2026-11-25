-- Prove2me | solution 1 for ContinuousLinearMap.exists_trace_repr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:06:21.474111+00:00
-- url     : https://prove2.me/submissions/8f25a44d-ef57-4728-8c17-6e8c5ea6fa7e

module
public import Mathlib.Analysis.Convex.Cone.Extension
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.LocallyConvex.HahnBanach
public import Mathlib.Analysis.Normed.Module.Span
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Definitions.Def_BasicResults_JohnIngredients

set_option autoImplicit true
@[expose] public section
public section
open scoped InnerProductSpace ComplexConjugate
open ContinuousLinearMap
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E] [CompleteSpace E]
namespace ContinuousLinearMap
theorem _root_.solution (f : (E →L[𝕜] E) →ₗ[𝕜] 𝕜) :
    ∃ G : E →L[𝕜] E, ∀ A : E →L[𝕜] E,
      f A = LinearMap.trace 𝕜 E ((A : E →ₗ[𝕜] E) ∘ₗ (G : E →ₗ[𝕜] E)) := by
  classical
  have : FiniteDimensional 𝕜 (E →L[𝕜] E) :=
    Module.Finite.equiv
      (LinearMap.toContinuousLinearMap : (E →ₗ[𝕜] E) ≃ₗ[𝕜] (E →L[𝕜] E))
  -- the pairing `G ↦ (A ↦ tr (A ∘ G))`, as a linear map into the dual
  set J : (E →L[𝕜] E) →ₗ[𝕜] Module.Dual 𝕜 (E →L[𝕜] E) :=
    { toFun := fun G =>
        { toFun := fun A => LinearMap.trace 𝕜 E ((A : E →ₗ[𝕜] E) ∘ₗ (G : E →ₗ[𝕜] E))
          map_add' := fun A B => by
            simp only [ContinuousLinearMap.toLinearMap_add, LinearMap.add_comp, map_add]
          map_smul' := fun c A => by
            simp only [ContinuousLinearMap.toLinearMap_smul, LinearMap.smul_comp, map_smul,
              RingHom.id_apply] }
      map_add' := fun G₁ G₂ => by
        ext A
        simp only [ContinuousLinearMap.toLinearMap_add, LinearMap.comp_add, map_add,
          LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
      map_smul' := fun c G => by
        ext A
        simp only [ContinuousLinearMap.toLinearMap_smul, LinearMap.comp_smul, map_smul,
          LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply, LinearMap.smul_apply] } with hJ
  -- injectivity: test against the adjoint
  have hJinj : Function.Injective J := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro G hG
    have h0 : LinearMap.trace 𝕜 E
        (((ContinuousLinearMap.adjoint G : E →L[𝕜] E) : E →ₗ[𝕜] E) ∘ₗ (G : E →ₗ[𝕜] E))
          = 0 := by
      have h := DFunLike.congr_fun hG (ContinuousLinearMap.adjoint G)
      simpa [hJ] using h
    rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis 𝕜 E)] at h0
    have hterm : ∀ i, ⟪stdOrthonormalBasis 𝕜 E i,
        ((((ContinuousLinearMap.adjoint G : E →L[𝕜] E) : E →ₗ[𝕜] E)
          ∘ₗ (G : E →ₗ[𝕜] E)) (stdOrthonormalBasis 𝕜 E i))⟫_𝕜
        = ((‖G (stdOrthonormalBasis 𝕜 E i)‖ : 𝕜) ^ 2) := fun i => by
      rw [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_coe,
        ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
    rw [Finset.sum_congr rfl fun i _ => hterm i] at h0
    -- a sum of squares of norms vanishes, so `G` kills an orthonormal basis
    have hreal : ∑ i, ‖G (stdOrthonormalBasis 𝕜 E i)‖ ^ 2 = 0 := by
      have h1 : ((∑ i, ‖G (stdOrthonormalBasis 𝕜 E i)‖ ^ 2 : ℝ) : 𝕜) = 0 := by
        push_cast
        exact h0
      exact_mod_cast h1
    have hzero : ∀ i, G (stdOrthonormalBasis 𝕜 E i) = 0 := by
      intro i
      have hi := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg _).mp hreal i
        (Finset.mem_univ i)
      exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hi)
    apply ContinuousLinearMap.coe_injective
    apply Module.Basis.ext (stdOrthonormalBasis 𝕜 E).toBasis
    intro i
    simp [hzero i]
  -- surjectivity by dimension count
  have hJsurj : Function.Surjective J := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    rw [LinearMap.finrank_range_of_inj hJinj, Subspace.dual_finrank_eq]
  obtain ⟨G, hG⟩ := hJsurj f
  exact ⟨G, fun A => (DFunLike.congr_fun hG A).symm⟩
end ContinuousLinearMap
