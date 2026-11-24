-- Prove2me | solution 1 for Formalism.CountingSumsFrames.isL_monomial_ltr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:38:18.388011+00:00
-- url     : https://prove2.me/submissions/39fc25cd-0573-4fba-a7ca-7cf69f7d4594

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
import Theorems.Thm_Formalism_CountingSumsFrames_ltr_isL

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
theorem _root_.solution (m : σ →₀ ℕ) (a : K) : IsL fs (monomial (ltr fs m) a) := by
  intro m' hm' v hv
  have e := MvPolynomial.support_monomial_subset hm'
  rw [Finset.mem_singleton] at e
  subst e
  exact ltr_isL fs m v hv
end Formalism.CountingSumsFrames
