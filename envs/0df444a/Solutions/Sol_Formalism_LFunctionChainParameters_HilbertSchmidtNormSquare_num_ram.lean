-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.num_ram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:28:36.214327+00:00
-- url     : https://prove2.me/submissions/3f466716-8253-4b6d-a923-04dee41d6674

import Definitions.Def_Formalism_SizeWindowBrackets_TraceSquareAndDiagBounds
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
noncomputable section
set_option maxHeartbeats 800000
namespace Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
theorem _root_.solution {s a t : ℝ} (hs0 : 0 < s) (hs : s ≤ 1 / 20) (ha : 0 ≤ a) (ha' : a ≤ s / 2)
    (ht : 0 ≤ t) (ht' : t ≤ 1 / 2) :
    (1 + 5 * s) * (1 - a) ^ 2 ≤ (1 + 5 * s + 3 * t) * (1 - a - t ^ 2 - t * a) ^ 2 := by
  have hk : 2 * (1 + 5 * s + 3 * t) * (t + a) ≤ 3 * (1 - a) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hs) ht, mul_nonneg (sub_nonneg.2 ht') ht,
      mul_nonneg (sub_nonneg.2 ha') ht, mul_nonneg (sub_nonneg.2 hs) ha, mul_nonneg hs0.le ht]
  have hb0 : 0 ≤ 1 - a := by linarith
  have hP0 : 0 ≤ 1 + 5 * s + 3 * t := by linarith
  nlinarith [mul_nonneg (mul_nonneg ht hb0) (sub_nonneg.2 hk), mul_nonneg hP0 (sq_nonneg (t ^ 2 + t * a))]
end Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
