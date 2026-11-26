-- Prove2me | solution 1 for FirstPassageLinearTransport.wordIncrementSum_eq_list
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:33:34.744151+00:00
-- url     : https://prove2.me/submissions/684c2f9c-43c6-410a-9f5a-dd058ae9d10b

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
theorem _root_.solution
    {r : ℕ} (x : Bool → ℝ) (v : Fin r → Bool) :
    wordIncrementSum x v = listIncrementSum x (List.ofFn v) := by
  induction r with
  | zero => simp [wordIncrementSum, listIncrementSum]
  | succ r ih =>
      rw [wordIncrementSum, Fin.sum_univ_succ, List.ofFn_succ,
        listIncrementSum_cons]
      change x (v 0) + (∑ i : Fin r, x (v i.succ)) =
        x (v 0) + listIncrementSum x (List.ofFn fun i => v i.succ)
      have htail := ih (fun i => v i.succ)
      unfold wordIncrementSum at htail
      rw [htail]
end FirstPassageLinearTransport
