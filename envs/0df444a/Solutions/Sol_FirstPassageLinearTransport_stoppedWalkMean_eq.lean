-- Prove2me | solution 1 for FirstPassageLinearTransport.stoppedWalkMean_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:51:32.526094+00:00
-- url     : https://prove2.me/submissions/86e39770-201d-4a62-83f8-89188f6e1538

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
    {p : ℝ} (x : Bool → ℝ) (lo hi : ℝ)
    (hcenter : bernoulliAverage p (x false) (x true) = 0) :
    ∀ r z, stoppedWalkMean p x lo hi r z = z := by
  intro r
  induction r with
  | zero => simp [stoppedWalkMean]
  | succ r ihr =>
      intro z
      by_cases hstop : z < lo ∨ hi ≤ z
      · simp [stoppedWalkMean, hstop]
      · simp only [stoppedWalkMean, hstop, if_false, ihr]
        unfold bernoulliAverage at hcenter ⊢
        nlinarith
end FirstPassageLinearTransport
