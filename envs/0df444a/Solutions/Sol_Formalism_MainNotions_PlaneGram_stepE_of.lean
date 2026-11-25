-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.stepE_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:24:54.517147+00:00
-- url     : https://prove2.me/submissions/68e9627c-3f0b-4d7f-a8f9-09e97f2ec689

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SumOnLetterApplyInl
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_ChOK_dg
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_ChOK_ddiv_all
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_sum_ldeg_div_add_le_sl
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_cge_digitPart
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_digitPart_add
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_gaAct_eq
import Theorems.Thm_Formalism_MainNotions_PlaneGram_cge_of_bge
import Theorems.Thm_Formalism_MainNotions_PlaneGram_cge_zero
import Theorems.Thm_Formalism_MainNotions_PlaneGram_v_unit_inv
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_mono


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
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution [CharZero K] (v : AddValuation K (WithTop ℚ)) (p : ℕ) (hV2 : V2 K) (hDER : DER K v p) :
    StepE K v p := by
  intro hD D hValid hH F hF hb M hM0 hMd ρ
  obtain ⟨hr, -, hc, -, -, -, hgu, hgs⟩ := hValid
  haveI : NeZero D.r := ⟨hr.ne'⟩
  have h0 : D.ChOK v p D.th (-D.n0 v) F := by
    refine ⟨F, 0, by rw [add_zero], ?_, cge_zero v _, fun ρ j i => hF.2.1 ρ j i⟩
    have := cge_of_bge hD hF.1 hb
    rw [zero_sub] at this
    exact this
  obtain ⟨T1, lam1, hl1, hf1⟩ := hgs 1 (Or.inl rfl)
  obtain ⟨T2, lam2, hl2, hf2⟩ := hgs (-1) (Or.inr rfl)
  have h1 := h0.dg hV2 D.ga (fun α => (hgu α).ge) T1 lam1 hl1
    (fun α => by have := hf1 α; rwa [zpow_one] at this)
  have h2 := h1.ddiv_all hV2 hDER hD hc M hM0
  have h3 := h2.dg hV2 (fun α => (D.ga α)⁻¹) (fun α => (v_unit_inv v (hgu α)).ge) T2 lam2 hl2
    (fun α => by have := hf2 α; rwa [zpow_neg_one] at this)
  obtain ⟨G0, E, hG, -, hE, hval⟩ := h3
  refine ⟨D.digitPart p ρ G0, D.digitPart p ρ E, ?_, fun j i => ?_, ?_⟩
  · rw [D.gaAct_eq, hG, D.digitPart_add]
  · refine vala_mono ?_ (hval ρ j i)
    have := D.sum_ldeg_div_add_le_sl p hD.prime.pos hr hH M hMd j i
    linarith
  · have := D.cge_digitPart p v ρ hE
    rwa [neg_add_eq_sub] at this
end Formalism.MainNotions.PlaneGram
