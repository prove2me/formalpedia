-- Prove2me | solution 1 for Formalism.CountingSumsFrames.pII0_basic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:04:54.603815+00:00
-- url     : https://prove2.me/submissions/ac8b092a-7652-4cd6-baf7-1265c3ca77ea

import Definitions.Def_Formalism_PolynomialDimension_StatementNum
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SecondParameterSizeBoundsHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.CountingSumsFrames
open Real
namespace Formalism.CountingSumsFrames
theorem _root_.solution (r N N₁ k : ℝ) (hr : 2 ≤ r) (hrN1 : r ≤ N₁) (hN1 : N₁ ^ 2 ≤ r * N)
    (hk : N₁ + 3 * r ≤ k) : r ≤ N ∧ 8 ≤ k ∧ N₁ + 1 ≤ 2 * r * N := by
  have h1 : r * r ≤ r * N := by nlinarith
  have hrN : r ≤ N := le_of_mul_le_mul_left h1 (by linarith)
  refine ⟨hrN, by linarith, ?_⟩
  nlinarith
end Formalism.CountingSumsFrames
