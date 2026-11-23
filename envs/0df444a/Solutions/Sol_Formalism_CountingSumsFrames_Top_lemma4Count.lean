-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Top.lemma4Count
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:37:54.209802+00:00
-- url     : https://prove2.me/submissions/9f92c095-f251-4bb4-9319-fd6f632ddee9

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_ExistsNonzeroExchangedMinorHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FrobeniusDetVanishingHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FockGaussComparisonHolds
import Definitions.Def_Formalism_PolynomialDimension_DetMulEqSumAdjugate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.Top
namespace Formalism.CountingSumsFrames.Top
theorem _root_.solution : Formalism.CountingSumsFrames.Lemma4Count := by
  intro N1 ntops m kQ c' al h
  have h1 := Nat.mul_le_mul_right (m + kQ + c') h
  calc ntops * (m + kQ + c') + (c' * al + 2 * c') ≤ N1 * (m + kQ + c') + (c' * al + 2 * c') :=
        Nat.add_le_add_right h1 _
    _ ≤ N1 * (m + kQ + c') + (c' * al + 2 * c') + (N1 * (c' * al + 2 * c') + (m + kQ + c')) :=
        Nat.le_add_right _ _
    _ = (N1 + 1) * (m + kQ + c' * al + 3 * c') := by ring
end Formalism.CountingSumsFrames.Top
