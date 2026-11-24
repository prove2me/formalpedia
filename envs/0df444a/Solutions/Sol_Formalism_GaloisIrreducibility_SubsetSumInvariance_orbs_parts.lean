-- Prove2me | solution 1 for Formalism.GaloisIrreducibility.SubsetSumInvariance.orbs_parts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:58:20.323935+00:00
-- url     : https://prove2.me/submissions/19ae1f93-8130-4e91-af5d-2c635de4f92a

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_PermSubSumInv

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
theorem _root_.solution (σ : Perm α) : (orbs σ).val.map Finset.card = σ.partition.parts := by
  have hdisj : Disjoint (σ.cycleFactorsFinset.image support) ((univ \ σ.support).image fun y => {y}) := by
    rw [Finset.disjoint_left]
    intro O h1 h2
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 h1
    obtain ⟨y, -, hy⟩ := Finset.mem_image.1 h2
    have h2le := (Perm.mem_cycleFactorsFinset_iff.1 hc).1.two_le_card_support
    rw [← hy, Finset.card_singleton] at h2le
    omega
  have hinj1 : Set.InjOn support (σ.cycleFactorsFinset : Set (Perm α)) := by
    intro c hc c' hc' h
    obtain ⟨a, ha⟩ := (Perm.mem_cycleFactorsFinset_iff.1 hc).1.nonempty_support
    rw [Perm.cycle_is_cycleOf ha hc, Perm.cycle_is_cycleOf (h ▸ ha) hc']
  have hinj2 : Set.InjOn (fun y : α => ({y} : Finset α)) ((univ \ σ.support : Finset α) : Set α) := by
    intro y _ z _ h
    exact Finset.singleton_injective h
  rw [orbs, ← Finset.disjUnion_eq_union _ _ hdisj, Finset.disjUnion_val, Multiset.map_add,
    Finset.image_val_of_injOn hinj1, Finset.image_val_of_injOn hinj2, Multiset.map_map, Multiset.map_map,
    Perm.parts_partition, Perm.cycleType_def]
  congr 1
  have : (Finset.card ∘ fun y : α => ({y} : Finset α)) = fun _ => 1 := by
    funext y
    simp
  rw [this, Multiset.map_const', Finset.card_val, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ]
end Formalism.GaloisIrreducibility.SubsetSumInvariance
