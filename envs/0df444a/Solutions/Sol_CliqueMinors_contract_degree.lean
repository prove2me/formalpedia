-- Prove2me | solution 1 for CliqueMinors.contract_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:33:45.959358+00:00
-- url     : https://prove2.me/submissions/e1901ac0-ea48-4ad5-b25f-466afa4766e3

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V : Type*}
open scoped Classical
variable [Fintype V]
namespace CliqueMinors
theorem _root_.solution {G : SimpleGraph V} {S : Finset V} {x y : V} (k : ℕ) (hxy : G.Adj x y)
    (hdeg : ∀ v ∈ S, k ≤ G.degree v)
    (hmerge : k ≤ (((G.neighborFinset x ∪ G.neighborFinset y).erase x).erase y).card)
    (hcommon : ∀ z, G.Adj x z → G.Adj y z → k + 1 ≤ G.degree z) :
    ∀ v ∈ S.erase y, k ≤ (contractG G x y).degree v := by
  intro v hv
  obtain ⟨hvy, hvS⟩ := Finset.mem_erase.1 hv
  rw [← card_neighborFinset_eq_degree]
  by_cases hvx : v = x
  · subst hvx
    refine hmerge.trans (Finset.card_le_card fun t ht => ?_)
    simp only [Finset.mem_erase, Finset.mem_union, mem_neighborFinset] at ht
    rw [mem_neighborFinset]
    refine ⟨Ne.symm ht.2.1, hvy, ht.1, ?_⟩
    rcases ht.2.2 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨rfl, h⟩)
  have hsub1 : (G.neighborFinset v).erase y ⊆ (contractG G x y).neighborFinset v := by
    intro t ht
    simp only [Finset.mem_erase, mem_neighborFinset] at ht
    rw [mem_neighborFinset]
    exact ⟨ht.2.ne, hvy, ht.1, Or.inl ht.2⟩
  by_cases hvy' : G.Adj v y
  · by_cases hvx' : G.Adj v x
    · have := hcommon v hvx'.symm hvy'.symm
      have h1 := Finset.card_le_card hsub1
      rw [Finset.card_erase_of_mem (by simpa using hvy'), card_neighborFinset_eq_degree] at h1
      omega
    · have hsub2 : insert x ((G.neighborFinset v).erase y) ⊆
          (contractG G x y).neighborFinset v := by
        refine Finset.insert_subset ?_ hsub1
        rw [mem_neighborFinset]
        exact ⟨hvx, hvy, hxy.ne, Or.inr (Or.inr ⟨rfl, hvy'.symm⟩)⟩
      have h1 := Finset.card_le_card hsub2
      rw [Finset.card_insert_of_notMem (by simp [hvx']),
        Finset.card_erase_of_mem (by simpa using hvy'), card_neighborFinset_eq_degree] at h1
      have := hdeg v hvS
      omega
  · have hsub : G.neighborFinset v ⊆ (contractG G x y).neighborFinset v := by
      intro t ht
      rw [mem_neighborFinset] at ht ⊢
      exact ⟨ht.ne, hvy, fun h => hvy' (h ▸ ht), Or.inl ht⟩
    exact (hdeg v hvS).trans ((card_neighborFinset_eq_degree G v).symm.le.trans
      (Finset.card_le_card hsub))
end CliqueMinors
