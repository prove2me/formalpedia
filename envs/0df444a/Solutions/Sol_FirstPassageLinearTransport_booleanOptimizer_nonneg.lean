-- Prove2me | solution 1 for FirstPassageLinearTransport.booleanOptimizer_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:38:33.423373+00:00
-- url     : https://prove2.me/submissions/18db920f-0490-4ca0-957c-4d9203474eb1

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
    0 ≤ booleanOptimizer t := by
  have hq : 0 < (1 / 2 : ℝ) - t := by linarith
  have hp : 0 < (1 / 2 : ℝ) + t := by linarith
  have hqp : (1 / 2 : ℝ) - t ≤ 1 / 2 + t := by linarith
  have hlog := Real.log_le_log hq hqp
  unfold booleanOptimizer
  linarith
end FirstPassageLinearTransport
