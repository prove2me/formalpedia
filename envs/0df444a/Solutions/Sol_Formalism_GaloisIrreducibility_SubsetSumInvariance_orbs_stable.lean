-- Prove2me | solution 1 for Formalism.GaloisIrreducibility.SubsetSumInvariance.orbs_stable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:12.014807+00:00
-- url     : https://prove2.me/submissions/4a3d6fc5-bdeb-40bb-a1d4-42c7c89d5688

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_PermSubSumInv
import Theorems.Thm_Formalism_GaloisIrreducibility_SubsetSumInvariance_fixed_of_not_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GaloisIrreducibility
open Formalism.GaloisIrreducibility.SubsetSumInvariance
open Equiv Equiv.Perm Finset
variable {α : Type} [Fintype α] [DecidableEq α]
namespace Formalism.GaloisIrreducibility.SubsetSumInvariance
theorem _root_.solution {σ : Perm α} {O : Finset α} (hO : O ∈ orbs σ) : ∀ x ∈ O, σ x ∈ O := by
  intro x hx
  rcases Finset.mem_union.1 hO with h | h
  · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 h
    rw [← (Perm.mem_cycleFactorsFinset_iff.1 hc).2 x hx]
    exact Perm.apply_mem_support.2 hx
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 h
    rw [Finset.mem_singleton] at hx ⊢
    subst hx
    exact fixed_of_not_mem (Finset.mem_sdiff.1 hy).2
end Formalism.GaloisIrreducibility.SubsetSumInvariance
