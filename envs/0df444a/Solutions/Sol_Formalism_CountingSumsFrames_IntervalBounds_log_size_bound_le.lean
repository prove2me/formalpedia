-- Prove2me | solution 1 for Formalism.CountingSumsFrames.IntervalBounds.log_size_bound_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:02:42.386384+00:00
-- url     : https://prove2.me/submissions/6a6b91ae-9218-4fe2-a8ea-8a29c717bf03

import Mathlib
import Definitions.Def_Formalism_PolynomialDimension_ApolarComparisonExponent
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_ParamsI
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_IntervalCleanDepthBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.CountingSumsFrames
open Formalism.CountingSumsFrames.IntervalBounds
open ParamsIProof
namespace Formalism.CountingSumsFrames.IntervalBounds
theorem _root_.solution (k lg kap1 : ℝ) (hk : 1 ≤ k) (hlg : 0 ≤ lg) (h : kap1 ≤ (k - 1) ^ 2 * lg) :
    kap1 ≤ k ^ 2 * lg := by
  have h1 : (k - 1) ^ 2 ≤ k ^ 2 := by nlinarith
  exact le_trans h (mul_le_mul_of_nonneg_right h1 hlg)
end Formalism.CountingSumsFrames.IntervalBounds
