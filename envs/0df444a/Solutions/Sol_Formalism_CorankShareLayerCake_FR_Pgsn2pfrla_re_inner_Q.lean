-- Prove2me | solution 1 for Formalism.CorankShareLayerCake.FR.Pgsn2pfrla.re_inner_Q
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:35:07.023998+00:00
-- url     : https://prove2.me/submissions/dfb289e6-a534-4a39-86c6-d3045164abad

import Mathlib
import Definitions.Def_Formalism_CorankShare_StatementFR
import Definitions.Def_Formalism_CorankShare_CorankShareProofs_SumNormSqLeHilbertSchmidt
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
private lemma re_inner_self_eq_norm_sq_corank_share {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] (x : G) :
    (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 :=
  inner_self_eq_norm_sq (𝕜 := ℂ) x
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
variable {ι : Type*} [Fintype ι] {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)]
    [∀ i, InnerProductSpace ℂ (V i)] [∀ i, FiniteDimensional ℂ (V i)]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
namespace Formalism.CorankShareLayerCake.FR.Pgsn2pfrla
theorem _root_.solution (c : ι → ℝ) (B : ∀ i, V i →ₗ[ℂ] H) (x : H) :
    (⟪x, frQ c B x⟫_ℂ).re = ∑ i, c i * ‖adjoint (B i) x‖ ^ 2 := by
  simp only [frQ, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    inner_sum, inner_smul_right, Complex.re_sum, Complex.re_ofReal_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← LinearMap.adjoint_inner_left (B i) (adjoint (B i) x) x, re_inner_self_eq_norm_sq_corank_share]
end Formalism.CorankShareLayerCake.FR.Pgsn2pfrla
