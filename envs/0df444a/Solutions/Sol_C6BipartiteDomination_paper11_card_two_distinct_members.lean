-- Prove2me | solution 1 for C6BipartiteDomination.paper11_card_two_distinct_members
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:04:27.070079+00:00
-- url     : https://prove2.me/submissions/d5ce3f64-98db-4e7d-8b29-728962e5b67e

import Definitions.Def_C6BipartiteDomination_PaperSection10
import Definitions.Def_C6BipartiteDomination_PaperSection11

set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {T : Finset V} (hT : T.card = 2) :
    ∃ a b, a ≠ b ∧ a ∈ T ∧ b ∈ T := by
  classical
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by rw [hT]; omega)
  have herase : (T.erase a).card = 1 := by
    calc
      (T.erase a).card = T.card - 1 := Finset.card_erase_of_mem ha
      _ = 1 := by rw [hT]
  obtain ⟨b, hbEq⟩ := Finset.card_eq_one.mp herase
  have hbErase : b ∈ T.erase a := by rw [hbEq]; simp
  exact ⟨a, b, (Finset.mem_erase.mp hbErase).1.symm, ha,
    (Finset.mem_erase.mp hbErase).2⟩
end C6BipartiteDomination
