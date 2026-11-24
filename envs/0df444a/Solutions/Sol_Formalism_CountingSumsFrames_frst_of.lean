-- Prove2me | solution 1 for Formalism.CountingSumsFrames.frst_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:37:28.982502+00:00
-- url     : https://prove2.me/submissions/c03a6bd8-ca45-4333-a756-ca5c228d6bbb

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
theorem _root_.solution {m : σ →₀ ℕ} (h : ∀ v, m v ≠ 0 → fs v) : frst fs m = m := by
  unfold frst
  exact (Finsupp.filter_eq_self_iff _ _).mpr h
end Formalism.CountingSumsFrames
