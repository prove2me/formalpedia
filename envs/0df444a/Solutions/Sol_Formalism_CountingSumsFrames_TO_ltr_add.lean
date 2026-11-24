-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.ltr_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:34:53.067257+00:00
-- url     : https://prove2.me/submissions/47bf62ee-3911-477d-9ca8-c7584f2d76e4

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open MvPolynomial Finset
variable {K : Type} [Field K] {σ : Type} [DecidableEq σ] (fs : σ → Prop) [DecidablePred fs]
namespace Formalism.CountingSumsFrames.TO
theorem _root_.solution (m m' : σ →₀ ℕ) : ltr fs (m + m') = ltr fs m + ltr fs m' := by
  unfold ltr
  exact Finsupp.filter_add
end Formalism.CountingSumsFrames.TO
