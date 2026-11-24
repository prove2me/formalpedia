-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.Tset_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:07:46.034197+00:00
-- url     : https://prove2.me/submissions/edc3e447-74c1-4c33-86d3-448ee1e2fdb3

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ProjKeepsLetter
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CardLinkIdxMulLe
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Tset_mono
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Tset_disjoint

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
theorem _root_.solution (x y : Fin D.J × Fin D.r) :
    D.Tset x.1 x.2 ⊆ D.Tset y.1 y.2 ∨ D.Tset y.1 y.2 ⊆ D.Tset x.1 x.2 ∨
      Disjoint (D.Tset x.1 x.2) (D.Tset y.1 y.2) := by
  obtain ⟨j, m⟩ := x
  obtain ⟨j', m'⟩ := y
  by_cases h : j = j'
  · subst h
    rcases le_total m m' with h | h
    · exact Or.inr (Or.inl (D.Tset_mono j h))
    · exact Or.inl (D.Tset_mono j h)
  · exact Or.inr (Or.inr (D.Tset_disjoint h m m'))
end Formalism.MainNotions.PlaneGram.TwistData
