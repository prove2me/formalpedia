-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.schur_scalar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:08:41.166949+00:00
-- url     : https://prove2.me/submissions/46730088-c107-42fb-bdd6-253b05a25c8e

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCentralIdempotent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
variable {G V : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution [Nontrivial V] (ρ : Representation ℂ G V)
    (h : ∀ W : Submodule ℂ V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → W = ⊥ ∨ W = ⊤)
    (a : G → ℂ) (ha : ∀ g k, a (k * g * k⁻¹) = a g) :
    ∃ μ : ℂ, (∑ g, a g • ρ g) = μ • (1 : Module.End ℂ V) := by
  set T : Module.End ℂ V := ∑ g, a g • ρ g with hT
  have hcomm : ∀ k, ρ k * T = T * ρ k := by
    intro k
    rw [hT, Finset.mul_sum, Finset.sum_mul]
    refine Fintype.sum_equiv (MulAut.conj k).toEquiv _ _ (fun g => ?_)
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, ha, mul_smul_comm,
      smul_mul_assoc, ← map_mul, inv_mul_cancel_right]
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue T
  refine ⟨μ, ?_⟩
  have hW : ∀ g, ∀ x ∈ Module.End.eigenspace T μ, ρ g x ∈ Module.End.eigenspace T μ := by
    intro g x hx
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    rw [← Module.End.mul_apply, ← hcomm g, Module.End.mul_apply, hx, map_smul]
  rcases h _ hW with h0 | h0
  · exfalso
    first
      | exact Module.End.hasEigenvalue_iff.1 hμ h0
      | exact hμ h0
      | (obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
         have hv1 := hv.1
         rw [h0] at hv1
         exact hv.2 ((Submodule.mem_bot ℂ).1 hv1))
  · refine LinearMap.ext fun x => ?_
    have hx : x ∈ Module.End.eigenspace T μ := by
      rw [h0]
      exact Submodule.mem_top
    rw [Module.End.mem_eigenspace_iff] at hx
    rw [hx]
    simp
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
