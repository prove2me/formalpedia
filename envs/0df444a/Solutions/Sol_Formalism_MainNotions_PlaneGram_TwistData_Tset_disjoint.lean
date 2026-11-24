-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.Tset_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:51:16.804828+00:00
-- url     : https://prove2.me/submissions/c70c0477-48f6-4d0a-b20e-b1354b8b1e84

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
theorem _root_.solution {j j' : Fin D.J} (h : j ≠ j') (m m' : Fin D.r) :
    Disjoint (D.Tset j m) (D.Tset j' m') := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  rw [mem_Tset] at hz hz'
  rcases hz with ⟨b, hb, rfl⟩ | ⟨m1, -, rfl⟩
  · rcases hz' with ⟨b', hb', e⟩ | ⟨m2, -, e⟩
    · have : b = b' := Sum.inl.inj e
      subst this
      exact h (hb.symm.trans hb')
    · cases e
  · rcases hz' with ⟨b', -, e⟩ | ⟨m2, -, e⟩
    · cases e
    · have := Sum.inr.inj e
      exact h (congrArg Prod.fst this)
end Formalism.MainNotions.PlaneGram.TwistData
