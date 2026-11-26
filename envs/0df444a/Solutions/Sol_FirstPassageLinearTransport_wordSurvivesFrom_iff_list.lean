-- Prove2me | solution 1 for FirstPassageLinearTransport.wordSurvivesFrom_iff_list
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:54:29.547945+00:00
-- url     : https://prove2.me/submissions/3fa89b00-f343-4fd3-81e2-60dbfbd5524f

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
    {r : ℕ} (lo : ℝ) (x : Bool → ℝ) (z : ℝ) (v : Fin r → Bool) :
    wordSurvivesFrom lo x r z v ↔
      listSurvivesFrom lo x z (List.ofFn v) := by
  induction r generalizing z with
  | zero => simp [wordSurvivesFrom, listSurvivesFrom]
  | succ r ih =>
      rw [List.ofFn_succ]
      simp only [wordSurvivesFrom, listSurvivesFrom]
      rw [ih]
end FirstPassageLinearTransport
