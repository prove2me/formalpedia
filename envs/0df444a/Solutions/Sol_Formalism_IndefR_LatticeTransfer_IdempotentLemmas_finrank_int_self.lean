-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.IdempotentLemmas.finrank_int_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:15:03.980747+00:00
-- url     : https://prove2.me/submissions/379c7f79-149d-46e8-8d11-50eaac4fcc86

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransfer
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinrankIntSelf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.LatticeTransfer
open Formalism.IndefR.TransferLatticeStatement
open Formalism.IndefR.LatticeTransfer.IdempotentLemmas
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
namespace Formalism.IndefR.LatticeTransfer.IdempotentLemmas
theorem _root_.solution {T : Type} [AddCommGroup T] [Module K T] [Nontrivial T]
    (τ : Representation K G T)
    (h : ∀ f : T →ₗ[K] T, (∀ g : G, f ∘ₗ τ g = τ g ∘ₗ f) → ∃ c : K, f = c • LinearMap.id) :
    finrank K (Representation.IntertwiningMap τ τ) = 1 := by
  have hne : Representation.IntertwiningMap.id τ ≠ 0 := by
    obtain ⟨v, hv⟩ := exists_ne (0 : T)
    intro h0
    apply hv
    have := congrArg (fun f : Representation.IntertwiningMap τ τ => f v) h0
    simpa using this
  rw [finrank_eq_one_iff_of_nonzero' _ hne]
  intro w
  obtain ⟨c, hc⟩ := h w.toLinearMap (fun g => w.isIntertwining' g)
  refine ⟨c, ?_⟩
  apply DFunLike.ext
  intro v
  have hv : w v = c • v := by
    rw [← Representation.IntertwiningMap.toLinearMap_apply, hc]
    simp
  rw [hv]
  simp
end Formalism.IndefR.LatticeTransfer.IdempotentLemmas
