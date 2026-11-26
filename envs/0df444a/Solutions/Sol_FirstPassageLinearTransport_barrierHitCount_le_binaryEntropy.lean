-- Prove2me | solution 1 for FirstPassageLinearTransport.barrierHitCount_le_binaryEntropy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:42:36.062359+00:00
-- url     : https://prove2.me/submissions/e35dcdbc-0215-4f2e-93c3-f16557053dc9

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_EntropyBarrier
import Theorems.Thm_FirstPassageLinearTransport_barrierHitCount_le_legendre
import Theorems.Thm_FirstPassageLinearTransport_booleanOptimizer_nonneg
import Theorems.Thm_FirstPassageLinearTransport_booleanLegendreRate_optimizer
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
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (t : ℝ) (M : ℕ) (ht0 : 0 ≤ t) (ht1 : t < 1 / 2) :
    (barrierHitCount (2 * t * M) M 0 : ℝ) ≤
      (2 : ℝ) ^ (M + 1) *
        Real.exp (-((M : ℝ) * binaryBarrierRate t)) := by
  have hraw := barrierHitCount_le_legendre
    t (booleanOptimizer t) M ht0 (booleanOptimizer_nonneg ht0 ht1)
  simpa [booleanLegendreRate_optimizer ht0 ht1] using hraw
end FirstPassageLinearTransport
