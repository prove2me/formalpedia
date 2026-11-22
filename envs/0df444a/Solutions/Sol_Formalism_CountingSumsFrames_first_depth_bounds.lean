-- Prove2me | solution 1 for Formalism.CountingSumsFrames.first_depth_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:41:54.06868+00:00
-- url     : https://prove2.me/submissions/993adf2b-930d-4857-99f2-2b39282b771e

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentHypOfIntervalHyp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Finset
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution {t : ℕ} {Y κ : ℝ} (hY : 1 ≤ Y) (hκ : 0 ≤ κ) :
    firstDepth t Y κ ≤ 2 * ((t : ℝ) + 1) * Y * κ ∧ κ ≤ firstDepth t Y κ := by
  unfold firstDepth
  have ht : (0:ℝ) ≤ t := Nat.cast_nonneg _
  have h1 : 0 ≤ (t:ℝ) * κ * (Y - 1) := mul_nonneg (mul_nonneg ht hκ) (by linarith)
  have h2 : 0 ≤ κ * (Y - 1) := mul_nonneg hκ (by linarith)
  have h3 : 0 ≤ (t:ℝ) * (Y * κ + κ) := by positivity
  have h4 : 0 ≤ κ * Y := by positivity
  constructor
  · nlinarith
  · linarith
end Formalism.CountingSumsFrames
