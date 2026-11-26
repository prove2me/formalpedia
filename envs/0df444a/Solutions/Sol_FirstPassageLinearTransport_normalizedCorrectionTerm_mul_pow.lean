-- Prove2me | solution 1 for FirstPassageLinearTransport.normalizedCorrectionTerm_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:23:04.729957+00:00
-- url     : https://prove2.me/submissions/459c229c-aa9d-4efe-a7a3-ffc6da3ba55c

import Mathlib.Algebra.Ring.GeomSum
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_Envelope
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_oddCount_mono
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
open scoped Real BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution {k n i : ℕ} (hi : i < k) :
    normalizedCorrectionTerm k n i * (3 : ℝ) ^ oddCount n k =
      parityDigitR n i *
        (3 : ℝ) ^ (oddCount n k - oddCount n (i + 1)) /
          (2 : ℝ) ^ (k - i) := by
  have hmono : oddCount n (i + 1) ≤ oddCount n k :=
    oddCount_mono (by omega)
  have hsplit : oddCount n k =
      oddCount n (i + 1) +
        (oddCount n k - oddCount n (i + 1)) := by omega
  unfold normalizedCorrectionTerm
  rw [hsplit, pow_add]
  field_simp
  simp
end FirstPassageLinearTransport
