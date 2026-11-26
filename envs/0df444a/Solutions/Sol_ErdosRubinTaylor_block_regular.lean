-- Prove2me | solution 1 for ErdosRubinTaylor.block_regular
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T21:49:33.03054+00:00
-- url     : https://prove2.me/submissions/7e234ad2-3317-4f83-b72d-e891a7677b5b


import Definitions.Def_ChoosabilityLib_ERTBasic
import Definitions.Def_ChoosabilityLib_ERTGallai
set_option autoImplicit true


open Finset SimpleGraph
open ErdosRubinTaylor
variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V]
theorem _root_.solution {T : Set V}
    (h : IsCliqueOn G T ∨ ∃ n, Odd n ∧ Nonempty (G.induce T ≃g cycleGraph n))
    (h2 : 2 ≤ T.ncard) {u v : V} (hu : u ∈ T) (hv : v ∈ T) : dIn G T u = dIn G T v := by
  classical
  have dc : ∀ n : ℕ, Odd n → Nonempty (G.induce T ≃g cycleGraph n) → ∀ u ∈ T, dIn G T u = 2 := by
    rintro n hn ⟨e⟩ u hu
    have h3 : 3 ≤ n := by
      have : T.ncard = n := by
        rw [← Nat.card_coe_set_eq, Nat.card_congr e.toEquiv, Nat.card_fin]
      rcases hn with ⟨k, hk⟩; omega
    have hd : (G.induce T).degree ⟨u, hu⟩ = 2 := by
      rw [← SimpleGraph.card_neighborSet_eq_degree, Fintype.card_congr (e.mapNeighborSet ⟨u, hu⟩),
        SimpleGraph.card_neighborSet_eq_degree]
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
      exact SimpleGraph.cycleGraph_degree_three_le
    rw [← hd, ← SimpleGraph.card_neighborFinset_eq_degree]
    unfold dIn
    refine (Finset.card_bij (fun w _ => w.1) ?_ ?_ ?_).symm
    · intro w hw
      simp at hw
      simp [hw]
    · intro a _ b _ h; exact Subtype.ext h
    · intro b hb
      simp at hb
      exact ⟨⟨b, hb.1⟩, by simp [hb.2], rfl⟩
  rcases h with h | ⟨n, hn, he⟩
  · have key : ∀ w ∈ T, dIn G T w = (T.toFinset.erase w).card := by
      intro w hw
      unfold dIn
      congr 1
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, Set.mem_toFinset]
      constructor
      · rintro ⟨hz, ha⟩; exact ⟨ha.ne', hz⟩
      · rintro ⟨hne, hz⟩; exact ⟨hz, h w hw z hz hne.symm⟩
    rw [key u hu, key v hv, Finset.card_erase_of_mem (by simpa using hu),
      Finset.card_erase_of_mem (by simpa using hv)]
  · rw [dc n hn he u hu, dc n hn he v hv]

