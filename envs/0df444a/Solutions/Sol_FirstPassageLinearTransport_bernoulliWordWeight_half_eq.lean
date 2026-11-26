-- Prove2me | solution 1 for FirstPassageLinearTransport.bernoulliWordWeight_half_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:34:50.858071+00:00
-- url     : https://prove2.me/submissions/73d63a84-2963-454a-9f26-bb6100f73565

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_bernoulliWordWeight_eq_support_card
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
theorem _root_.solution {m : ℕ} (v : Fin m → Bool) :
    bernoulliWordWeight (1 / 2) v = (1 / 2 : ℝ) ^ m := by
  rw [bernoulliWordWeight_eq_support_card]
  norm_num only [one_div, one_sub_div, Nat.cast_ofNat]
  rw [← pow_add]
  congr 1
  have hcard : (boolSupport v).card ≤ m := by
    simpa using Finset.card_le_card (Finset.subset_univ (boolSupport v))
  omega
end FirstPassageLinearTransport
