-- Prove2me | solution 1 for Formalism.CountingSumsFrames.ltr_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:37:29.039349+00:00
-- url     : https://prove2.me/submissions/63393e44-83c0-4714-82ef-1364f30e3cc8

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
theorem _root_.solution (m m' : σ →₀ ℕ) : ltr fs (m + m') = ltr fs m + ltr fs m' := by
  unfold ltr
  exact Finsupp.filter_add
end Formalism.CountingSumsFrames
