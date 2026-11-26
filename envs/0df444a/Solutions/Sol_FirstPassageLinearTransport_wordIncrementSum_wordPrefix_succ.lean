-- Prove2me | solution 1 for FirstPassageLinearTransport.wordIncrementSum_wordPrefix_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:54:50.274409+00:00
-- url     : https://prove2.me/submissions/feb8c606-f6b4-46a2-9a41-cd6a5b45f0c6

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
    {r : ℕ} (x : Bool → ℝ) (v : Fin (r + 1) → Bool)
    (j : Fin (r + 1)) :
    wordIncrementSum x (wordPrefix v j.succ) =
      x (v 0) + wordIncrementSum x
        (wordPrefix (fun i => v i.succ) j) := by
  rw [show wordPrefix v j.succ = Fin.cons (v 0)
      (wordPrefix (fun i => v i.succ) j) by
    funext i
    refine Fin.cases ?_ ?_ i
    · simp [wordPrefix]
    · intro k
      simp [wordPrefix]]
  rw [wordIncrementSum_cons]
end FirstPassageLinearTransport
