-- Prove2me | solution 1 for C6BipartiteDomination.minimal_deficient_neighbor_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:43:40.51477+00:00
-- url     : https://prove2.me/submissions/935fd994-07e4-4827-9ae8-1c28065f6da5

import Definitions.Def_C6BipartiteDomination_A2
import Definitions.Def_C6BipartiteDomination_A3
import Theorems.Thm_C6BipartiteDomination_neighborsIn_mono_left

set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    {X W : Finset V}
    (hXne : X.Nonempty)
    (hdef : (neighborsIn G X W).card < X.card)
    (hmin : ∀ Y, Y ⊆ X → (neighborsIn G Y W).card < Y.card → X.card ≤ Y.card) :
    (neighborsIn G X W).card + 1 = X.card := by
  classical
  obtain ⟨x, hx⟩ := hXne
  have hsub : X.erase x ⊆ X := Finset.erase_subset x X
  have hnotdef : ¬ (neighborsIn G (X.erase x) W).card < (X.erase x).card := by
    intro hbad
    have hcard := hmin (X.erase x) hsub hbad
    have hlt : (X.erase x).card < X.card := Finset.card_erase_lt_of_mem hx
    omega
  have hlow : (X.erase x).card ≤ (neighborsIn G (X.erase x) W).card := by omega
  have hmono : neighborsIn G (X.erase x) W ⊆ neighborsIn G X W :=
    neighborsIn_mono_left G (Finset.erase_subset x X)
  have hlow' : (X.erase x).card ≤ (neighborsIn G X W).card :=
    le_trans hlow (Finset.card_le_card hmono)
  have herase : (X.erase x).card + 1 = X.card := by
    rw [Finset.card_erase_of_mem hx]
    omega
  omega
end C6BipartiteDomination
