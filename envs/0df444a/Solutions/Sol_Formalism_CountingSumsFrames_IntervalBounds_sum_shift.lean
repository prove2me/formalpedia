-- Prove2me | solution 1 for Formalism.CountingSumsFrames.IntervalBounds.sum_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:40:35.872215+00:00
-- url     : https://prove2.me/submissions/13286413-cb6f-4227-8fb1-95dd5a171088

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
theorem _root_.solution {ι : Type} (T : Finset ι) (f g : ι → ℝ) (e Nr : ℝ) (he : 0 ≤ e)
    (hT : (T.card : ℝ) ≤ Nr) (h : ∀ y ∈ T, f y ≤ g y + e) :
    ∑ y ∈ T, f y ≤ ∑ y ∈ T, g y + Nr * e := by
  calc ∑ y ∈ T, f y ≤ ∑ y ∈ T, (g y + e) := Finset.sum_le_sum h
    _ = ∑ y ∈ T, g y + T.card * e := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ y ∈ T, g y + Nr * e := by
        have := mul_le_mul_of_nonneg_right hT he
        linarith
end Formalism.CountingSumsFrames.IntervalBounds
