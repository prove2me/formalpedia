-- Prove2me | solution 1 for FirstPassageLinearTransport.wordSurvivesFrom_of_prefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:55:28.632256+00:00
-- url     : https://prove2.me/submissions/36bd3b95-7636-44a4-8c39-e530169d1a9b

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_wordIncrementSum_wordPrefix_succ
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
    {r : ℕ} {lo z : ℝ} {x : Bool → ℝ} {v : Fin r → Bool}
    (h : ∀ j : Fin (r + 1),
      lo ≤ z + wordIncrementSum x (wordPrefix v j)) :
    wordSurvivesFrom lo x r z v := by
  induction r generalizing z with
  | zero =>
      simpa [wordSurvivesFrom] using h (0 : Fin 1)
  | succ r ih =>
      constructor
      · simpa only [wordIncrementSum_wordPrefix_zero, add_zero] using
          h (0 : Fin (r + 2))
      · apply ih
        intro j
        have hj := h j.succ
        rw [wordIncrementSum_wordPrefix_succ] at hj
        linarith
end FirstPassageLinearTransport
