-- Prove2me | solution 1 for Formalism.CountingSumsFrames.frst_add_ltr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:34:12.778799+00:00
-- url     : https://prove2.me/submissions/e47587ac-51ba-42f1-a141-4b8fd9bcbc67

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open MvPolynomial Finset
variable {K : Type} [Field K] {σ : Type} [DecidableEq σ] (fs : σ → Prop) [DecidablePred fs]
namespace Formalism.CountingSumsFrames
theorem _root_.solution (m : σ →₀ ℕ) : frst fs m + ltr fs m = m := by
  unfold frst ltr
  exact Finsupp.filter_pos_add_filter_neg _ _
end Formalism.CountingSumsFrames
