-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.frst_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:34:31.23119+00:00
-- url     : https://prove2.me/submissions/1de8b28a-db34-4b1e-95bb-6324defd036b

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
theorem _root_.solution {m : σ →₀ ℕ} (h : ∀ v, m v ≠ 0 → fs v) : frst fs m = m := by
  ext v
  unfold frst
  rw [Finsupp.filter_apply]
  split_ifs with hv
  · rfl
  · by_contra hne
    exact hv (h v (Ne.symm hne))
end Formalism.CountingSumsFrames.TO
