-- Prove2me | solution 1 for Formalism.CountingSumsFrames.ltr_isL
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:35:42.761992+00:00
-- url     : https://prove2.me/submissions/d1899d90-f3fa-4765-8148-a268a9b98848

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
theorem _root_.solution (m : σ →₀ ℕ) : ∀ v, ltr fs m v ≠ 0 → ¬ fs v := by
  intro v hv h
  apply hv
  unfold ltr
  rw [Finsupp.filter_apply_neg (fun v => ¬ fs v) m (not_not.mpr h)]
end Formalism.CountingSumsFrames
