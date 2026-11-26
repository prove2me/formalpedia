-- Prove2me | solution 1 for FirstPassageLinearTransport.exp_neg_booleanOptimizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:39:48.437667+00:00
-- url     : https://prove2.me/submissions/3a1884c1-dc31-4916-9074-82e39941cffc

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_EntropyBarrier

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1 / 2) :
    Real.exp (-booleanOptimizer t) =
      Real.sqrt ((1 / 2 - t) / (1 / 2 + t)) := by
  have hq : 0 < (1 / 2 : ℝ) - t := by linarith
  have hp : 0 < (1 / 2 : ℝ) + t := by linarith
  rw [show -booleanOptimizer t =
      (Real.log (1 / 2 - t) - Real.log (1 / 2 + t)) / 2 by
        unfold booleanOptimizer
        ring]
  rw [Real.exp_half, Real.exp_sub, Real.exp_log hq, Real.exp_log hp]
end FirstPassageLinearTransport
