-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.ChOK.ddiv_all
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:59:27.051843+00:00
-- url     : https://prove2.me/submissions/0afa0f05-9173-415e-9bdc-273861abe370

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SumOnLetterApplyInl
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_sum_onLetter_apply_inr
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_sum_onLetter_apply_inl
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_ChOK_ddiv_finset

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
variable [CharZero K] (D : TwistData K) (v : AddValuation K (WithTop ℚ)) (p : ℕ)
variable {D v p}
variable (D p)
variable {D p}
namespace Formalism.MainNotions.PlaneGram.TwistData
namespace ChOK
theorem _root_.solution [NeZero D.r] (hV2 : V2 K) (hDER : DER K v p) (hD : DVRHyp v p) (hc : 1 ≤ D.c)
    {θ : (j : Fin D.J) → Fin (D.nch j) → ℝ} {a : ℝ}
    {G : MvPolynomial (D.OL × Fin D.r) K} (h : D.ChOK v p θ a G) (M : D.EA)
    (hM : ∀ b a, M (Sum.inl b, a) = 0) :
    D.ChOK v p (fun j i => θ j i - ∑ t,
        (if t.1 = D.aux₃ j then (ldeg M (Sum.inr t) : ℝ) / (D.P p t : ℝ) + D.c else 0)) a
      (Formalism.MainNotions.PlaneGram.ddiv M G) := by
  have h1 := h.ddiv_finset hV2 hDER hD hc M Finset.univ
  have e : (∑ t, onLetter (Sum.inr t : D.OL) (letE M (Sum.inr t))) = M := by
    ext ⟨i, a⟩
    rcases i with b | t
    · rw [D.sum_onLetter_apply_inl M _ b a, hM]
    · rw [D.sum_onLetter_apply_inr M _ t a, if_pos (Finset.mem_univ _)]
  rwa [e] at h1
end ChOK
end Formalism.MainNotions.PlaneGram.TwistData
