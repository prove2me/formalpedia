-- Prove2me | solution 1 for C6BipartiteDomination.minimal_deficient_subset_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:43:51.45914+00:00
-- url     : https://prove2.me/submissions/80e352ad-c6d0-4fd8-880a-dba9e5d2e774

import Definitions.Def_C6BipartiteDomination_A2
import Definitions.Def_C6BipartiteDomination_A3
import Theorems.Thm_C6BipartiteDomination_mem_neighborsIn
import Theorems.Thm_C6BipartiteDomination_neighborsIn_self_subset

set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    {X W S : Finset V}
    (hAcard : (neighborsIn G X W).card + 1 = X.card)
    (hmin : ∀ Y, Y ⊆ X → (neighborsIn G Y W).card < Y.card → X.card ≤ Y.card)
    (hS : S ⊆ neighborsIn G X W) (hSne : S.Nonempty) :
    (neighborsIn G S X).card ≥ S.card + 1 := by
  classical
  let T := neighborsIn G S X
  let Y := X \ T
  have hTsub : T ⊆ X := by
    exact neighborsIn_self_subset G S X
  have hTne : T.Nonempty := by
    obtain ⟨s, hs⟩ := hSne
    have hsA : s ∈ neighborsIn G X W := hS hs
    obtain ⟨w, hwX, hAdj⟩ := (mem_neighborsIn G X W s).mp hsA |>.2
    refine ⟨w, ?_⟩
    rw [mem_neighborsIn]
    exact ⟨hwX, s, hs, hAdj.symm⟩
  have hYsub : Y ⊆ X := Finset.sdiff_subset
  have hYcard : Y.card + T.card = X.card := by
    dsimp [Y]
    exact Finset.card_sdiff_add_card_eq_card hTsub
  have hYlt : Y.card < X.card := by
    have hTpos : 0 < T.card := Finset.card_pos.mpr hTne
    omega
  have hYnotbad : ¬ (neighborsIn G Y W).card < Y.card := by
    intro hbad
    have := hmin Y hYsub hbad
    omega
  have hYdom : Y.card ≤ (neighborsIn G Y W).card := by omega
  have hNWsub : neighborsIn G Y W ⊆ (neighborsIn G X W) \ S := by
    intro w hw
    rw [mem_neighborsIn] at hw
    rcases hw.2 with ⟨y, hy, hAdj⟩
    have hyX : y ∈ X := hYsub hy
    simp only [Finset.mem_sdiff]
    refine ⟨?_, ?_⟩
    · rw [mem_neighborsIn]
      exact ⟨hw.1, y, hyX, hAdj⟩
    intro hws
    have hyT : y ∈ T := by
      dsimp [T]
      rw [mem_neighborsIn]
      exact ⟨hyX, w, hws, hAdj.symm⟩
    have hyNotT : y ∉ T := (Finset.mem_sdiff.mp hy).2
    exact hyNotT hyT
  have hSsub : S ⊆ neighborsIn G X W := hS
  have hNWcard : (neighborsIn G Y W).card ≤ ((neighborsIn G X W) \ S).card :=
    Finset.card_le_card hNWsub
  have hAminus : ((neighborsIn G X W) \ S).card + S.card = (neighborsIn G X W).card :=
    Finset.card_sdiff_add_card_eq_card hSsub
  dsimp [T] at hYcard ⊢
  omega
end C6BipartiteDomination
