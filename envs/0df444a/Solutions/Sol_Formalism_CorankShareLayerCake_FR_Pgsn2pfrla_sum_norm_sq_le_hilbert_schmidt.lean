-- Prove2me | solution 1 for Formalism.CorankShareLayerCake.FR.Pgsn2pfrla.sum_norm_sq_le_hilbert_schmidt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:34.729169+00:00
-- url     : https://prove2.me/submissions/e9cce0f2-4ef7-4530-855a-8388c200d383

import Mathlib
import Definitions.Def_Formalism_CorankShare_StatementFR
import Definitions.Def_Formalism_CorankShare_CorankShareProofs_SumNormSqLeHilbertSchmidt
import Theorems.Thm_Formalism_CorankShareLayerCake_FR_Pgsn2pfrla_norm_inner_swap
import Theorems.Thm_Formalism_CorankShareLayerCake_FR_Pgsn2pfrla_sum_adj_eq
import Theorems.Thm_Formalism_CorankShareLayerCake_FR_Pgsn2pfrla_hilbert_schmidt_eq_basis_sum
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
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
namespace Formalism.CorankShareLayerCake.FR.Pgsn2pfrla
theorem _root_.solution {κ : Type*} [Fintype κ] (A : E →ₗ[ℂ] F) {g : κ → E} (hg : Orthonormal ℂ g) :
    ∑ l, ‖A (g l)‖ ^ 2 ≤ hs2 A := by
  rw [hilbert_schmidt_eq_basis_sum A (stdOrthonormalBasis ℂ E), ← sum_adj_eq A (stdOrthonormalBasis ℂ E) (stdOrthonormalBasis ℂ F)]
  have h1 : ∀ l, ‖A (g l)‖ ^ 2 = ∑ n, ‖⟪g l, adjoint A (stdOrthonormalBasis ℂ F n)⟫_ℂ‖ ^ 2 := by
    intro l
    rw [← orthonormalBasis_sum_norm_inner_sq_eq_norm_sq (stdOrthonormalBasis ℂ F)]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [LinearMap.adjoint_inner_right, norm_inner_swap]
  simp only [h1]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum (fun n _ => Orthonormal.sum_inner_products_le _ hg)
end Formalism.CorankShareLayerCake.FR.Pgsn2pfrla
