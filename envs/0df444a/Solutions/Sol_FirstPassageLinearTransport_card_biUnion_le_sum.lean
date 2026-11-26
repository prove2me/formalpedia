-- Prove2me | solution 1 for FirstPassageLinearTransport.card_biUnion_le_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:01:05.706305+00:00
-- url     : https://prove2.me/submissions/d7f08544-c03c-49ae-93dc-2718de76604e

import Definitions.Def_FirstPassageLinearTransport_FirstPassage
import Definitions.Def_FirstPassageLinearTransport_Transport
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
namespace FirstPassageLinearTransport
theorem _root_.solution {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → Finset β) :
    (s.biUnion f).card ≤ ∑ a ∈ s, (f a).card := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.biUnion_insert]
      calc
        (f a ∪ s.biUnion f).card ≤ (f a).card + (s.biUnion f).card :=
          Finset.card_union_le _ _
        _ ≤ (f a).card + ∑ x ∈ s, (f x).card := by omega
        _ = ∑ x ∈ insert a s, (f x).card := by simp [ha]
end FirstPassageLinearTransport
