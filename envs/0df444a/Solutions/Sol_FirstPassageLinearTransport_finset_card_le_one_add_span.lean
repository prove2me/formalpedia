-- Prove2me | solution 1 for FirstPassageLinearTransport.finset_card_le_one_add_span
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:07:48.934018+00:00
-- url     : https://prove2.me/submissions/ef4d5779-8478-498e-af7d-766a6b5816b8

import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_FirstPassage
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero


attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber

set_option autoImplicit true
open FirstPassageLinearTransport
namespace FirstPassageLinearTransport
theorem _root_.solution (s : Finset ℕ) (hs : s.Nonempty) :
    (s.card : ℚ) ≤
      1 + (s.max' hs : ℚ) - (s.min' hs : ℚ) := by
  let a := s.min' hs
  let b := s.max' hs
  have hab : a ≤ b := by
    rcases hs with ⟨x, hx⟩
    exact (s.min'_le x hx).trans (s.le_max' x hx)
  have hsub : s ⊆ Finset.Icc a b := by
    intro x hx
    exact Finset.mem_Icc.mpr ⟨s.min'_le x hx, s.le_max' x hx⟩
  have hcardNat : s.card ≤ b + 1 - a := by
    have := Finset.card_le_card hsub
    simpa using this
  have hcast : (s.card : ℚ) ≤ ((b + 1 - a : ℕ) : ℚ) := by
    exact_mod_cast hcardNat
  have hsubcast : ((b + 1 - a : ℕ) : ℚ) = (b : ℚ) + 1 - (a : ℚ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_add]
    norm_num
  change (s.card : ℚ) ≤ 1 + (b : ℚ) - (a : ℚ)
  linarith
end FirstPassageLinearTransport
