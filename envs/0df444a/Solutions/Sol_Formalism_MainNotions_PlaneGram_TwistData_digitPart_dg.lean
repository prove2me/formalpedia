-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.digitPart_dg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:37:25.418501+00:00
-- url     : https://prove2.me/submissions/bd7bdf55-e058-4106-bb7f-4d8959be29f0

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_emb_liftE
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_digitPart_add
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_digitPart_monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_dg_monomial


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
variable {K : Type} [Field K]
open Formalism.MainNotions.PlaneGram.TwistData
variable (D : TwistData K) (p : ℕ)
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (ρ : D.Tau → Fin D.r → ℕ) (f : D.EA → K) (G : MvPolynomial (D.OL × Fin D.r) K) :
    D.digitPart p ρ (dg f G) = dg (fun ζ => f (D.emb p ρ ζ)) (D.digitPart p ρ G) := by
  refine MvPolynomial.induction_on' G (fun α c => ?_) (fun F₁ F₂ h₁ h₂ => ?_)
  · rw [Formalism.MainNotions.PlaneGram.dg_monomial, digitPart_monomial, digitPart_monomial]
    by_cases h : D.InClass p ρ α
    · rw [if_pos h, if_pos h, Formalism.MainNotions.PlaneGram.dg_monomial, D.emb_liftE p ρ α h]
    · rw [if_neg h, if_neg h, map_zero]
  · rw [map_add, digitPart_add, digitPart_add, map_add, h₁, h₂]
end Formalism.MainNotions.PlaneGram.TwistData
