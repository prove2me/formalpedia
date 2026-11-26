-- Prove2me | solution 1 for FirstPassageLinearTransport.booleanLegendreRate_optimizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:41:53.018537+00:00
-- url     : https://prove2.me/submissions/beaef3ab-e69e-4136-b291-3fd3d6370849

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_EntropyBarrier
import Theorems.Thm_FirstPassageLinearTransport_log_cosh_booleanOptimizer

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1 / 2) :
    booleanLegendreRate t (booleanOptimizer t) = binaryBarrierRate t := by
  rw [booleanLegendreRate, binaryBarrierRate,
    log_cosh_booleanOptimizer ht0 ht1]
  unfold booleanOptimizer Real.binEntropy
  rw [Real.log_inv, Real.log_inv]
  ring
end FirstPassageLinearTransport
