-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.costA_choose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:41:37.382735+00:00
-- url     : https://prove2.me/submissions/1d92281d-b797-4440-8fc7-f9bef096ea16

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SumOnLetterApplyInl
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_costM_ok
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_costM_choose
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_emb_inl
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_emb_inr
import Theorems.Thm_Formalism_MainNotions_PlaneGram_cost_choose_affine
import Theorems.Thm_Formalism_MainNotions_PlaneGram_divE_apply
import Theorems.Thm_Formalism_MainNotions_PlaneGram_letE_apply
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
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution [NeZero D.r] (hV2 : V2 K) (x : D.OL × Fin D.r) (k : ℕ) :
    D.CostA p k (fun α => ((α x).choose k : K)) := by
  intro ρ
  obtain ⟨i, a⟩ := x
  rcases i with b | t
  · simp only [emb_inl]
    exact D.costM_choose hV2 (D.mb b, a) k
  · simp only [emb_inr]
    exact cost_choose_affine D.costM_ok (fun ζ => ζ (D.mw t, a))
      (fun k => D.costM_choose hV2 (D.mw t, a) k) (ρ t a) (D.P p t) k
end Formalism.MainNotions.PlaneGram.TwistData
