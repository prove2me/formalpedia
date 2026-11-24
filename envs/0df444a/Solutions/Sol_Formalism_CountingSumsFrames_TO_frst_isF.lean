-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.frst_isF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:34:30.60481+00:00
-- url     : https://prove2.me/submissions/18721e9c-b013-45e3-8a70-7206b218c6fb

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
theorem _root_.solution (m : σ →₀ ℕ) : ∀ v, frst fs m v ≠ 0 → fs v := by
  intro v hv
  unfold frst at hv
  rw [Finsupp.filter_apply] at hv
  by_contra h
  exact hv (if_neg h)
end Formalism.CountingSumsFrames.TO
