-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.kapL_dUp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:06:53.245012+00:00
-- url     : https://prove2.me/submissions/3215c0a0-849e-4175-96ae-4ec09481fbcf

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_TestBoundOfRhoAndNormSets
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_GlobalTheory

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
open Formalism.MainNotions.PlaneGram.TwistData
variable {K : Type} [Field K] (D : TwistData K)
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (p : ℕ) : kapL p D.r D.dUp = kapL p D.r D.dO := by
  unfold kapL dUp dO
  first
    | (simp [Fintype.sum_sum_type]; done)
    | (simp [Fintype.sum_sum_type]; rfl)
    | (simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]; simp; rfl)
end Formalism.MainNotions.PlaneGram.TwistData
