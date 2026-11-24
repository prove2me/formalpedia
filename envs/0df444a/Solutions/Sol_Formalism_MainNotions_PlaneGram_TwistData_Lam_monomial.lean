-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.Lam_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:39:02.76194+00:00
-- url     : https://prove2.me/submissions/5ab3f156-c0d2-4ba0-8acb-2428a2cc58e8

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ProjKeepsLetter
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_TestBoundOfRhoAndNormSets
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_ph_monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_dg_monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_fock_monomial_right
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
theorem _root_.solution (p : ℕ) (F : MvPolynomial (D.OL × Fin D.r) K) (ζ : D.EM) (c : K) :
    D.abelian₂ p F (monomial ζ c) =
      F.coeff (D.phE p ζ) * (D.ga (D.phE p ζ) * c) * (fact (D.phE p ζ) : K) := by
  unfold abelian₂; rw [ph_monomial, gaAct_eq_dg, dg_monomial, fock_monomial_right]
end Formalism.MainNotions.PlaneGram.TwistData
