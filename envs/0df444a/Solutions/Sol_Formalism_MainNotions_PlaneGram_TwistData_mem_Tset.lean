-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.mem_Tset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:45:14.323246+00:00
-- url     : https://prove2.me/submissions/23410566-9a5d-40cc-8c5d-b20010e0e5b3

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ProjKeepsLetter
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CardLinkIdxMulLe

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
theorem _root_.solution (j : Fin D.J) (m : Fin D.r) (z : D.OL) :
    z ∈ D.Tset j m ↔ (∃ b, D.seg b = j ∧ z = Sum.inl b) ∨ (∃ m', m < m' ∧ z = Sum.inr (j, m')) := by
  simp only [Tset, LLj, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨b, hb, rfl⟩ | ⟨m', hm', rfl⟩)
    · exact Or.inl ⟨b, hb, rfl⟩
    · exact Or.inr ⟨m', hm', rfl⟩
  · rintro (⟨b, hb, rfl⟩ | ⟨m', hm', rfl⟩)
    · exact Or.inl ⟨b, hb, rfl⟩
    · exact Or.inr ⟨m', hm', rfl⟩
end Formalism.MainNotions.PlaneGram.TwistData
