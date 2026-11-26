-- Prove2me | solution 1 for FirstPassageLinearTransport.card_shellMaximalParityBad_le_binaryEntropy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:43:25.772846+00:00
-- url     : https://prove2.me/submissions/5a916129-263c-4e91-b924-4558a0e6e4a9

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_EntropyBarrier
import Theorems.Thm_FirstPassageLinearTransport_barrierHitCount_le_binaryEntropy
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_card_shellBarrierHit
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shellMaximalParityBad_subset_hit
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
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (t : ℝ) (M : ℕ) (ht0 : 0 ≤ t) (ht1 : t < 1 / 2) :
    ((shellMaximalParityBad M (t * M)).card : ℝ) ≤
      (2 : ℝ) ^ (M + 1) *
        Real.exp (-((M : ℝ) * binaryBarrierRate t)) := by
  have hcard :
      (shellMaximalParityBad M (t * M)).card ≤
        (shellBarrierHit M (t * M)).card :=
    Finset.card_le_card (shellMaximalParityBad_subset_hit M (t * M))
  have hcardR :
      ((shellMaximalParityBad M (t * M)).card : ℝ) ≤
        ((shellBarrierHit M (t * M)).card : ℝ) := by
    exact_mod_cast hcard
  rw [card_shellBarrierHit] at hcardR
  have htail := barrierHitCount_le_binaryEntropy t M ht0 ht1
  exact hcardR.trans (by simpa [mul_assoc] using htail)
end FirstPassageLinearTransport
