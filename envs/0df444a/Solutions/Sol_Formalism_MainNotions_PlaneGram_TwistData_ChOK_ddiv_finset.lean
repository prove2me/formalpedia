-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.ChOK.ddiv_finset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:36:18.920182+00:00
-- url     : https://prove2.me/submissions/74914d57-568e-4fbc-b5c4-ac5c4ba52bc2

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SumOnLetterApplyInl
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_ChOK_mono
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_sum_onLetter_apply_inr
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_sum_onLetter_apply_inl
import Theorems.Thm_Formalism_MainNotions_PlaneGram_absE_letE
import Theorems.Thm_Formalism_MainNotions_PlaneGram_ddiv_ddiv_of_disjoint
import Theorems.Thm_Formalism_MainNotions_PlaneGram_divE_apply
import Theorems.Thm_Formalism_MainNotions_PlaneGram_letE_apply
import Theorems.Thm_Formalism_MainNotions_PlaneGram_onLetter_apply
import Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_ddiv_zero__7224b7af6ae9
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
variable {D p}
namespace Formalism.MainNotions.PlaneGram.TwistData
namespace ChOK
theorem _root_.solution [NeZero D.r] (hV2 : V2 K) (hDER : DER K v p) (hD : DVRHyp v p) (hc : 1 ≤ D.c)
    {θ : (j : Fin D.J) → Fin (D.nch j) → ℝ} {a : ℝ}
    {G : MvPolynomial (D.OL × Fin D.r) K} (h : D.ChOK v p θ a G) (M : D.EA) (s : Finset D.Tau) :
    D.ChOK v p (fun j i => θ j i - ∑ t ∈ s,
        (if t.1 = D.aux₃ j then (ldeg M (Sum.inr t) : ℝ) / (D.P p t : ℝ) + D.c else 0)) a
      (Formalism.MainNotions.PlaneGram.ddiv (∑ t ∈ s, onLetter (Sum.inr t : D.OL) (letE M (Sum.inr t))) G) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, sub_zero]
    rw [ddiv_zero']
    exact h
  | insert t s ht ih =>
    have h1 := ih.ddiv hV2 hDER hD hc t (letE M (Sum.inr t))
    rw [ddiv_ddiv_of_disjoint] at h1
    · rw [Finset.sum_insert ht]
      refine h1.mono fun j i => ?_
      rw [Finset.sum_insert ht, absE_letE]
      linarith
    · rintro ⟨i, a⟩
      rcases i with b | t'
      · right; exact D.sum_onLetter_apply_inl M s b a
      · by_cases htt : t' = t
        · right
          rw [D.sum_onLetter_apply_inr M s t' a, if_neg (htt ▸ ht)]
        · left
          rw [onLetter_apply, if_neg (fun hh => htt (Sum.inr.inj hh))]
end ChOK
end Formalism.MainNotions.PlaneGram.TwistData
