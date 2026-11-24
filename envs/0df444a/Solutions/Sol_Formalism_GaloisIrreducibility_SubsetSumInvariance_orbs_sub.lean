-- Prove2me | solution 1 for Formalism.GaloisIrreducibility.SubsetSumInvariance.orbs_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:12.965811+00:00
-- url     : https://prove2.me/submissions/f29f28e7-7398-41b5-9ff1-04fd86198b7c

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_PermSubSumInv
import Theorems.Thm_Formalism_GaloisIrreducibility_SubsetSumInvariance_pow_stable

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
theorem _root_.solution {σ : Perm α} {A : Finset α} (hA : ∀ x ∈ A, σ x ∈ A) {O : Finset α}
    (hO : O ∈ orbs σ) {x : α} (hxO : x ∈ O) (hxA : x ∈ A) : O ⊆ A := by
  intro y hy
  rcases Finset.mem_union.1 hO with h | h
  · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 h
    have hcx : c = σ.cycleOf x := Perm.cycle_is_cycleOf hxO hc
    rw [hcx, Perm.mem_support_cycleOf_iff] at hy
    obtain ⟨i, hi⟩ := hy.1.exists_nat_pow_eq
    rw [← hi]
    exact pow_stable hA i x hxA
  · obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 h
    rw [Finset.mem_singleton] at hy hxO
    rw [hy, ← hxO]
    exact hxA
end Formalism.GaloisIrreducibility.SubsetSumInvariance
