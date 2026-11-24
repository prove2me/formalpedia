-- Prove2me | solution 1 for Formalism.CountingSumsFrames.frst_isF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:37:54.207171+00:00
-- url     : https://prove2.me/submissions/422a5496-f85f-4928-ae6e-a4c0cb3ae0a2

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
theorem _root_.solution (m : σ →₀ ℕ) : ∀ v, frst fs m v ≠ 0 → fs v := by
  intro v hv
  by_contra h
  apply hv
  unfold frst
  rw [Finsupp.filter_apply_neg _ _ h]
end Formalism.CountingSumsFrames
