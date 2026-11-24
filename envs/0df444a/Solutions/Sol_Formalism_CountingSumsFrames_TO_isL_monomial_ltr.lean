-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.isL_monomial_ltr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:38:18.515994+00:00
-- url     : https://prove2.me/submissions/86ca8b41-cf05-4509-ae9e-483d7c8f197b

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_TO_ltr_isL

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
theorem _root_.solution (m : σ →₀ ℕ) (a : K) : IsL fs (monomial (ltr fs m) a) := by
  intro m' hm' v hv
  have := support_monomial_subset hm'
  rw [Finset.mem_singleton] at this
  subst this
  exact ltr_isL fs m v hv
end Formalism.CountingSumsFrames.TO
