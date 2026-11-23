-- Prove2me | solution 1 for Formalism.CountingSumsFrames.digit_double_count
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:09.80794+00:00
-- url     : https://prove2.me/submissions/5d15c6cc-c033-41ae-833c-e8eeca10898a

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentBoundThreeHolds
import Theorems.Thm_Formalism_CountingSumsFrames_digit_vectors_count
import Theorems.Thm_Formalism_CountingSumsFrames_digitDoubleCount_of

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
namespace Formalism.CountingSumsFrames
theorem _root_.solution : DigitDoubleCount := digitDoubleCount_of digit_vectors_count
end Formalism.CountingSumsFrames
