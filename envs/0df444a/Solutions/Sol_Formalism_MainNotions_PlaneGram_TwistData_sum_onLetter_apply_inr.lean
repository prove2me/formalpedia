-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.sum_onLetter_apply_inr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:39:33.046671+00:00
-- url     : https://prove2.me/submissions/ddf681cd-490a-4ba6-9841-4749e439b0e0

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SumOnLetterApplyInl
import Theorems.Thm_Formalism_MainNotions_PlaneGram_divE_apply
import Theorems.Thm_Formalism_MainNotions_PlaneGram_letE_apply
import Theorems.Thm_Formalism_MainNotions_PlaneGram_onLetter_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.PlaneGram.divE_apply
attribute [local simp] Formalism.MainNotions.PlaneGram.letE_apply



set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K]
open Formalism.MainNotions.PlaneGram.TwistData
variable [CharZero K] (D : TwistData K) (v : AddValuation K (WithTop ℚ)) (p : ℕ)
variable {D v p}
variable (D p)
variable {D p}
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (D : TwistData K) (M : D.EA) (s : Finset D.Tau) (t : D.Tau) (a : Fin D.r) :
    (∑ t' ∈ s, onLetter (Sum.inr t' : D.OL) (letE M (Sum.inr t'))) (Sum.inr t, a) =
      if t ∈ s then M (Sum.inr t, a) else 0 := by
  classical
  rw [Finsupp.finsetSum_apply]
  simp only [onLetter_apply, letE_apply, Sum.inr.injEq]
  rw [Finset.sum_ite_eq]
end Formalism.MainNotions.PlaneGram.TwistData
