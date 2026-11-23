-- Prove2me | solution 1 for Formalism.CountingSumsFrames.factProd_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:50:14.307539+00:00
-- url     : https://prove2.me/submissions/92886853-ab02-4cdc-98de-dfdbe3e8d84e

import Definitions.Def_Formalism_PolynomialDimension_FrameSum
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FockGaussComparisonHolds

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
theorem _root_.solution {σ : Type} [Fintype σ] (α : σ →₀ ℕ) : factProd α ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => Nat.factorial_ne_zero _
end Formalism.CountingSumsFrames
