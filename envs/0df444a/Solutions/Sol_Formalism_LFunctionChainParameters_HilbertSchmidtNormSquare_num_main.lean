-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.num_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:28:35.464117+00:00
-- url     : https://prove2.me/submissions/41c20a98-f597-4ee3-924e-da82cf97e04a

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
theorem _root_.solution {s η0 η1 a : ℝ} (hs0 : 0 < s) (hs : s ≤ 1 / 4) (hη0 : -1 ≤ η0) (hη0' : η0 ≤ s / 2)
    (hη1' : η1 ≤ s / 2) (_hL : 0 ≤ 1 + η1) (ha : 0 ≤ a) (ha' : a ≤ s / 2) :
    (1 + η1) * ((1 + η0) + (1 + a) ^ 2 * s) ≤ (1 + 5 * s) * (1 - a) ^ 2 := by
  have hX0 : 0 ≤ (1 + η0) + (1 + a) ^ 2 * s :=
    add_nonneg (by linarith) (mul_nonneg (sq_nonneg _) hs0.le)
  have hsq : (1 + a) ^ 2 ≤ (1 + s / 2) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 ha') (by linarith : (0:ℝ) ≤ 2 + a + s / 2)]
  have hXY : (1 + η0) + (1 + a) ^ 2 * s ≤ (1 + s / 2) + (1 + s / 2) ^ 2 * s := by
    nlinarith [mul_le_mul_of_nonneg_right hsq hs0.le]
  have s1 : (1 + η1) * ((1 + η0) + (1 + a) ^ 2 * s) ≤ (1 + s / 2) * ((1 + η0) + (1 + a) ^ 2 * s) :=
    mul_le_mul_of_nonneg_right (by linarith) hX0
  have s2 : (1 + s / 2) * ((1 + η0) + (1 + a) ^ 2 * s)
      ≤ (1 + s / 2) * ((1 + s / 2) + (1 + s / 2) ^ 2 * s) :=
    mul_le_mul_of_nonneg_left hXY (by linarith)
  have s3 : (1 + s / 2) * ((1 + s / 2) + (1 + s / 2) ^ 2 * s) ≤ (1 + 5 * s) * (1 - s / 2) ^ 2 := by
    nlinarith [mul_nonneg hs0.le (by linarith : (0:ℝ) ≤ 1 / 4 - s),
      mul_nonneg (pow_nonneg hs0.le 3) (by linarith : (0:ℝ) ≤ 1 / 4 - s), pow_pos hs0 3, pow_pos hs0 2]
  have hsq2 : (1 - s / 2) ^ 2 ≤ (1 - a) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 ha') (by linarith : (0:ℝ) ≤ 2 - a - s / 2)]
  have s4 : (1 + 5 * s) * (1 - s / 2) ^ 2 ≤ (1 + 5 * s) * (1 - a) ^ 2 :=
    mul_le_mul_of_nonneg_left hsq2 (by linarith)
  linarith
end Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
