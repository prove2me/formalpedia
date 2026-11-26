-- Prove2me | solution 1 for FirstPassageLinearTransport.adjustableBarrierDisplacement_lt_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:41:30.665803+00:00
-- url     : https://prove2.me/submissions/9393207a-15ac-46d0-b0a6-dac91a01ea48

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_FirstPassageLinearTransport_AdjustableEnvelope
import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_AdjustableBarrierDensity
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_logTwoThree_pos
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
    {lambda t : ℝ} (hlambda : lambda ≤ 1) (ht0 : 0 ≤ t) (htA : t < a0) :
    adjustableBarrierDisplacement lambda t < 1 / 2 := by
  have hlt : lambda * t < a0 :=
    (mul_le_mul_of_nonneg_right hlambda ht0).trans_lt (by simpa using htA)
  rw [show (1 / 2 : ℝ) = a0 / logTwoThree by
    unfold a0
    field_simp [ne_of_gt logTwoThree_pos]]
  exact (div_lt_div_iff_of_pos_right logTwoThree_pos).2 hlt
end FirstPassageLinearTransport
