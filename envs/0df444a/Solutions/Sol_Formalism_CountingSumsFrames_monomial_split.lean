-- Prove2me | solution 1 for Formalism.CountingSumsFrames.monomial_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:37:55.182547+00:00
-- url     : https://prove2.me/submissions/d8c70bc4-1a1b-4ad3-86de-dc3d83f17bf0

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
import Theorems.Thm_Formalism_CountingSumsFrames_frst_add_ltr

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
theorem _root_.solution (m : σ →₀ ℕ) (a : K) :
    monomial m a = monomial (frst fs m) a * monomial (ltr fs m) 1 := by
  rw [MvPolynomial.monomial_mul, frst_add_ltr, mul_one]
end Formalism.CountingSumsFrames
