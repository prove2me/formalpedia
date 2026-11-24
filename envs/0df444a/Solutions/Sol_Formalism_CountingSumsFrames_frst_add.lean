-- Prove2me | solution 1 for Formalism.CountingSumsFrames.frst_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:37:05.520384+00:00
-- url     : https://prove2.me/submissions/3568278f-0d41-4931-a972-2ce647db11b4

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
theorem _root_.solution (m m' : σ →₀ ℕ) : frst fs (m + m') = frst fs m + frst fs m' := by
  unfold frst
  exact Finsupp.filter_add
end Formalism.CountingSumsFrames
