-- Prove2me | solution 1 for FirstPassageLinearTransport.ofFn_rev
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:33:33.892884+00:00
-- url     : https://prove2.me/submissions/9242b027-dd7e-4b74-92b1-04dcc7525076

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
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
theorem _root_.solution {r : ℕ} (v : Fin r → Bool) :
    List.ofFn (fun i => v (Fin.rev i)) = (List.ofFn v).reverse := by
  apply List.ext_get
  · simp
  · intro n hleft hright
    simp only [List.length_ofFn] at hleft
    rw [List.get_reverse']
    · simp only [List.get_ofFn]
      congr
      apply Fin.ext
      simp [Fin.rev]
      omega
    · simp
      omega
end FirstPassageLinearTransport
