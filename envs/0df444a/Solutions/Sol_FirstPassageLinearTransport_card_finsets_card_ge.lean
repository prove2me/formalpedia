-- Prove2me | solution 1 for FirstPassageLinearTransport.card_finsets_card_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:50:45.930841+00:00
-- url     : https://prove2.me/submissions/a321e5d4-d0db-47b0-b9eb-cf9ff819090c

import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Interval.Finset.Nat
import Definitions.Def_FirstPassageLinearTransport_EntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution (r k : ℕ) (hk : k ≤ r) :
    Fintype.card {s : Finset (Fin r) // k ≤ s.card} = binomialUpperTail r k := by
  classical
  rw [Fintype.card_subtype]
  let s : Finset (Finset (Fin r)) := Finset.univ.filter fun u => k ≤ u.card
  have hs :
      s.card = ∑ j ∈ Finset.Icc k r, (s.filter fun u => u.card = j).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro u hu
    have hku : k ≤ u.card := by simpa [s] using hu
    exact Finset.mem_Icc.mpr ⟨hku, card_finset_fin_le u⟩
  rw [show (Finset.univ.filter fun u : Finset (Fin r) => k ≤ u.card).card = s.card by rfl,
    hs]
  unfold binomialUpperTail
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_Icc.mp hj
  calc
    (s.filter fun u => u.card = j).card =
        Fintype.card {u : Finset (Fin r) // u.card = j} := by
      rw [Fintype.card_subtype]
      congr 1
      ext u
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨by omega, h⟩
    _ = r.choose j := by
      simpa using Fintype.card_finset_len (Fin r) j
end FirstPassageLinearTransport
