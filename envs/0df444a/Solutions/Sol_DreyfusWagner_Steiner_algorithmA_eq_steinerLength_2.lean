-- Prove2me | solution 2 for DreyfusWagner.Steiner.algorithmA_eq_steinerLength
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T14:54:35.560984+00:00
-- url     : https://prove2.me/submissions/204a0cd4-de79-4a55-b6ec-3677b555f9d8

import Mathlib
import Definitions.Def_DreyfusWagner_Steiner_Branch
import Definitions.Def_DreyfusWagner_Steiner_AlgorithmA
import Theorems.Thm_DreyfusWagner_Steiner_steinerTree_isAcyclic
import Theorems.Thm_DreyfusWagner_Steiner_steinerLength_pair_eq_pathDist
import Theorems.Thm_DreyfusWagner_Steiner_tableA_eq_steinerLength

-- carved verbatim out of submission e79de325-bc11-4400-bb86-16a3f52959b0, lines 725-745

section
open Finset SimpleGraph
open DreyfusWagner.Steiner

theorem solution {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ℓ : Sym2 V → ℝ)
    (hpos : ∀ e ∈ G.edgeSet, 0 < ℓ e) (hconn : G.Connected)
    (Y : Finset V) (hY : 3 ≤ Y.card) (q : V) (hq : q ∈ Y) :
    algorithmA G ℓ Y q = steinerLength G ℓ Y := by
  classical
  have hc : 2 ≤ (Y.erase q).card := by rw [card_erase_of_mem hq]; omega
  have hne : (Y.erase q).Nonempty := card_pos.mp (by omega)
  have ht := DreyfusWagner.Steiner.tableA_eq_steinerLength G ℓ hpos hconn (Y.erase q) hne q
  rw [insert_erase hq] at ht
  calc
    algorithmA G ℓ Y q = tableA (pathDist G ℓ) (Y.erase q) q := by
      rw [algorithmA, tableA, dif_neg (by omega : ¬(Y.erase q).card ≤ 1)]
      apply Finset.inf_congr rfl
      intro k hk
      congr 1
      exact (Finset.inf_attach _ _).symm
    _ = steinerLength G ℓ Y := ht

end
