-- Prove2me | solution 1 for FirstPassageLinearTransport.card_shellMaximalParityBad_adjustable_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:44:15.27099+00:00
-- url     : https://prove2.me/submissions/5d5095ce-8513-4816-a49d-557eaa084ac4

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_FirstPassageLinearTransport_AdjustableEnvelope
import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_AdjustableBarrierDensity
import Theorems.Thm_FirstPassageLinearTransport_adjustableBarrierHeight_eq_displacement_mul
import Theorems.Thm_FirstPassageLinearTransport_adjustableBarrierDisplacement_nonneg
import Theorems.Thm_FirstPassageLinearTransport_adjustableBarrierDisplacement_lt_half
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_card_shellMaximalParityBad_le_binaryEntropy
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
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {lambda t : ℝ} (M : ℕ)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (ht0 : 0 ≤ t) (htA : t < a0) :
    ((shellMaximalParityBad M
      (adjustableBarrierHeight lambda t M)).card : ℝ) ≤
      (2 : ℝ) ^ (M + 1) *
        Real.exp (-((M : ℝ) *
          binaryBarrierRate (adjustableBarrierDisplacement lambda t))) := by
  have hnonneg := adjustableBarrierDisplacement_nonneg hlambda0 ht0
  have hhalf := adjustableBarrierDisplacement_lt_half hlambda1 ht0 htA
  have hraw := card_shellMaximalParityBad_le_binaryEntropy
    (adjustableBarrierDisplacement lambda t) M hnonneg hhalf
  simpa [adjustableBarrierHeight_eq_displacement_mul] using hraw
end FirstPassageLinearTransport
