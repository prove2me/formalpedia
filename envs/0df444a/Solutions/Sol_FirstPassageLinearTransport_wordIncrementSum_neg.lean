-- Prove2me | solution 1 for FirstPassageLinearTransport.wordIncrementSum_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:32:18.312984+00:00
-- url     : https://prove2.me/submissions/6e96b6bd-6205-4df7-9827-4ea3f73f79fe

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
    wordIncrementSum (fun bit ↦ -x bit) v = -wordIncrementSum x v := by
  unfold wordIncrementSum
  simpa only [Finset.sum_neg_distrib]
end FirstPassageLinearTransport
