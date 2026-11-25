-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.Lam_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:18:03.486467+00:00
-- url     : https://prove2.me/submissions/23ac1d9e-6cd3-4cb4-af38-9e951eb874c0

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ProjKeepsLetter
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_TestBoundOfRhoAndNormSets
import Theorems.Thm_Formalism_MainNotions_PlaneGram_fock_sub_right
import Theorems.Thm_Formalism_MainNotions_PlaneGram_gaAct_eq_dg


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
theorem _root_.solution (p : ℕ) (F : MvPolynomial (D.OL × Fin D.r) K) (Z W : MvPolynomial (D.ML × Fin D.r) K) :
    D.abelian₂ p F (Z - W) = D.abelian₂ p F Z - D.abelian₂ p F W := by
  unfold abelian₂; simp only [gaAct_eq_dg, map_sub, fock_sub_right]
end Formalism.MainNotions.PlaneGram.TwistData
