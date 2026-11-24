-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.letter_module_minus
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:19.523609+00:00
-- url     : https://prove2.me/submissions/1e6c8097-aa4c-416e-98e0-c2511fe9546d

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondEmbedMulFirstEmbedApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_comm_RhtE
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_rtt_RhtE
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_rtt_mul_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_det_mul_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_detAt_RhtE
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_comm_diag
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_RhtE_herm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_herm_minus
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_eU_MU
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_diagScalar_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_diagScalar_conjTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_form_herm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_herm_transpose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_star_eU
import Theorems.Thm_Formalism_FourierDecayAlt_P_exchange_relation_minus


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Wd.LetterMinus := by
  intro K A S _ _ _ _ _ _ _ _ Ω RR TT q b Yb hM hRR hTT hYb hsYb
  have he : Wd4.MU (eU b : Fin 2 → Fin 2 → SlopeTestRemainingChoices S A) := Wd4.eU_MU b
  have hform : star (RR * ins b (TT Yb)ᵀ) = RR * ins b (TT Yb)ᵀ :=
    Wd4.form_herm hRR (fun i j => hTT Yb j i) (Wd4.herm_transpose (hM.herm Yb hYb hsYb))
  have hc : ∀ Y Y' i j k l, Commute (Wd4.RhtE (eU b) (Yb - Y) i j) (TT Y' k l) :=
    fun Y Y' i j k l => Wd4.comm_RhtE (Yb - Y) (TT Y' k l) (fun r s => hTT Y' k l r s) i j
  refine ⟨hform, ?_, ?_, ?_, ?_⟩
  · rintro Y ⟨hY, -⟩ hsY
    show (d0 (RR * ins b (TT Yb)ᵀ) * (Rht0 b (Yb - Y) * TT Y))ᴴ =
      d0 (RR * ins b (TT Yb)ᵀ) * (Rht0 b (Yb - Y) * TT Y)
    rw [Wd4.diagScalar_mul]
    refine Wd4.herm_minus _ _ _ _ ?_ ?_ (hM.herm Y hY hsY) ?_ ?_ ?_
    · rw [Wd4.diagScalar_conjTranspose, hM.form_herm]
    · rw [← Wd4.diagScalar_mul, Wd4.diagScalar_conjTranspose, hform]
    · exact Wd4.RhtE_herm (Wd1.star_eU b) (Yb - Y) (by rw [star_sub, hsY, hsYb])
    · exact Wd4.comm_diag _ RR (Wd4.comm_RhtE (Yb - Y) RR hRR)
    · exact exchange_relation_minus K A S Ω RR TT q b Y Yb hM hTT hY hYb
  · rintro Y ⟨hY, -⟩ Y' ⟨hY', -⟩
    exact Wd4.rtt_mul_at (fun Y => Wd4.RhtE (eU b) (Yb - Y)) TT Y Y' (Wd4.rtt_RhtE he Yb Y Y')
      (hM.rtt Y hY Y' hY') hc
  · rintro Y ⟨hY, hY1⟩ ⟨hY', hY1'⟩
    have h := Wd4.det_mul_at (fun Y => Wd4.RhtE (eU b) (Yb - Y)) TT _ q Y
      (Wd4.detAt_RhtE he Yb Y hY1 hY1') (hM.det Y hY hY') hc
    simp only [mul_comm _ (q _)] at h
    exact h
  · intro Y hsY
    simp only [star_mul', star_div₀, star_sub, star_one, hsY, hsYb, hM.q_real Y hsY]
end Formalism.FourierDecayAlt.P
