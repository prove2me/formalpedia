-- Prove2me | solution 1 for Formalism.CorankShareLayerCake.FR.Pgsn2pfrla.W_upper
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:34:15.424799+00:00
-- url     : https://prove2.me/submissions/5013a19d-df7c-4102-b957-cc5499ba5e3e

import Mathlib
import Definitions.Def_Formalism_CorankShare_StatementFR
import Definitions.Def_Formalism_CorankShare_CorankShareProofs_SumNormSqLeHilbertSchmidt
import Theorems.Thm_Formalism_CorankShareLayerCake_FR_Pgsn2pfrla_norm_inner_swap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.CorankShareLayerCake.FR
namespace Pgsn2pfrla
open Finset Module LinearMap
open scoped InnerProductSpace
section gen
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
private lemma orthonormalBasis_sum_norm_inner_sq_eq_norm_sq {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ G) (x : G) : ∑ i, ‖⟪b i, x⟫_ℂ‖ ^ 2 = ‖x‖ ^ 2 :=
  b.sum_sq_norm_inner_right x
end gen
section fam
variable {ι : Type*} [Fintype ι] {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)]
    [∀ i, InnerProductSpace ℂ (V i)] [∀ i, FiniteDimensional ℂ (V i)]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
end fam
section wup
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
end wup
end Pgsn2pfrla
open Finset Module LinearMap Pgsn2pfrla
open scoped InnerProductSpace
end Formalism.CorankShareLayerCake.FR
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.CorankShareLayerCake Formalism.CorankShareLayerCake.FR
open Formalism.CorankShareLayerCake.FR.Pgsn2pfrla
open Finset Module LinearMap
open scoped InnerProductSpace
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
namespace Formalism.CorankShareLayerCake.FR.Pgsn2pfrla
theorem _root_.solution (B : V →ₗ[ℂ] H) (N : Submodule ℂ V) {κ : Type*} [Fintype κ] {g : κ → H}
    (hg : Orthonormal ℂ g) (hperp : ∀ l, ∀ n ∈ N, ⟪B n, g l⟫_ℂ = 0) :
    ∑ l, ‖adjoint B (g l)‖ ^ 2 ≤ ∑ m, ‖B ((stdOrthonormalBasis ℂ Nᗮ m : V))‖ ^ 2 := by
  have hmem : ∀ l, adjoint B (g l) ∈ Nᗮ := by
    intro l
    rw [Submodule.mem_orthogonal]
    intro n hn
    rw [LinearMap.adjoint_inner_right, hperp l n hn]
  have h1 : ∀ l, ‖adjoint B (g l)‖ ^ 2 = ∑ m, ‖⟪g l, B ((stdOrthonormalBasis ℂ Nᗮ m : V))⟫_ℂ‖ ^ 2 := by
    intro l
    have h := orthonormalBasis_sum_norm_inner_sq_eq_norm_sq (stdOrthonormalBasis ℂ Nᗮ) ⟨adjoint B (g l), hmem l⟩
    have hn : ‖(⟨adjoint B (g l), hmem l⟩ : Nᗮ)‖ = ‖adjoint B (g l)‖ := rfl
    rw [hn] at h
    rw [← h]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    have hi : ⟪stdOrthonormalBasis ℂ Nᗮ m, (⟨adjoint B (g l), hmem l⟩ : Nᗮ)⟫_ℂ
        = ⟪(stdOrthonormalBasis ℂ Nᗮ m : V), adjoint B (g l)⟫_ℂ := rfl
    rw [hi, LinearMap.adjoint_inner_right, norm_inner_swap]
  simp only [h1]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum (fun m _ => Orthonormal.sum_inner_products_le _ hg)
end Formalism.CorankShareLayerCake.FR.Pgsn2pfrla
