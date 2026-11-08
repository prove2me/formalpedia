-- Prove2me | solution 1 for CombOpt.TJoin.proposition_5_24
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T22:31:53.63903+00:00
-- url     : https://prove2.me/submissions/46d3fab3-f989-4279-ba2a-47d7480bd488

import Mathlib
import Definitions.Def_CombOpt_TJoin_Graph
import Definitions.Def_CombOpt_TJoin_Graph_cut
import Definitions.Def_CombOpt_TJoin_Graph_IsTJoin

open scoped symmDiff

namespace Aux_CTJ524

theorem card_symmDiff_mod {α : Type*} [DecidableEq α] (X Y : Finset α) :
    (X ∆ Y).card % 2 = (X.card + Y.card) % 2 := by
  have h1 := Finset.card_sdiff_add_card_inter X Y
  have h2 := Finset.card_sdiff_add_card_inter Y X
  have h3 : (X ∆ Y).card = (X \ Y).card + (Y \ X).card := by
    rw [symmDiff_def, Finset.sup_eq_union, Finset.card_union_of_disjoint disjoint_sdiff_sdiff]
  rw [Finset.inter_comm] at h2
  omega

theorem inter_symmDiff {α : Type*} [DecidableEq α] (A B C : Finset α) :
    (A ∆ B) ∩ C = (A ∩ C) ∆ (B ∩ C) := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_symmDiff]
  tauto

end Aux_CTJ524

open CombOpt.TJoin Aux_CTJ524 in
theorem solution {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : CombOpt.TJoin.Graph V E) (T T' : Finset V) (hT : Even T.card) (hT' : Even T'.card)
    (J J' : Finset E) (hJ' : G.IsTJoin T' J') :
    G.IsTJoin T J ↔ G.IsTJoin (T ∆ T') (J ∆ J') := by
  have hv : ∀ v : V, ((J ∆ J') ∩ G.cut {v}).card % 2 =
      ((J ∩ G.cut {v}).card + (J' ∩ G.cut {v}).card) % 2 ∧
      ((T ∆ T') ∩ {v}).card % 2 = ((T ∩ {v}).card + (T' ∩ {v}).card) % 2 := by
    intro v
    rw [inter_symmDiff, inter_symmDiff]
    exact ⟨card_symmDiff_mod _ _, card_symmDiff_mod _ _⟩
  unfold CombOpt.TJoin.Graph.IsTJoin at hJ' ⊢
  simp only [Nat.ModEq] at hJ' ⊢
  constructor
  · intro h v
    have h1 := h v
    have h2 := hJ' v
    have h3 := hv v
    omega
  · intro h v
    have h1 := h v
    have h2 := hJ' v
    have h3 := hv v
    omega
