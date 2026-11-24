-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.Lam_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:51:28.962791+00:00
-- url     : https://prove2.me/submissions/f3eb88bf-d14c-43bf-a196-89838e41c914

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ProjKeepsLetter
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_TestBoundOfRhoAndNormSets
import Theorems.Thm_Formalism_MainNotions_PlaneGram_fock_smul_right
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
theorem _root_.solution (p : ℕ) (F : MvPolynomial (D.OL × Fin D.r) K) (a : K) (Z : MvPolynomial (D.ML × Fin D.r) K) :
    D.abelian₂ p F (a • Z) = a * D.abelian₂ p F Z := by
  unfold abelian₂; simp only [gaAct_eq_dg, map_smul, fock_smul_right]
end Formalism.MainNotions.PlaneGram.TwistData
