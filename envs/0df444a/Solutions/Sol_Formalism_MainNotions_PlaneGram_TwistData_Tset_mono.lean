-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.Tset_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:51:18.471897+00:00
-- url     : https://prove2.me/submissions/7b0f1213-9521-49b5-91de-a819019289fd

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ProjKeepsLetter
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CardLinkIdxMulLe
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_mem_Tset

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
theorem _root_.solution (j : Fin D.J) {m m' : Fin D.r} (h : m ≤ m') : D.Tset j m' ⊆ D.Tset j m := by
  intro z hz
  rw [mem_Tset] at hz ⊢
  rcases hz with hz | ⟨m'', hm'', rfl⟩
  · exact Or.inl hz
  · exact Or.inr ⟨m'', lt_of_le_of_lt h hm'', rfl⟩
end Formalism.MainNotions.PlaneGram.TwistData
