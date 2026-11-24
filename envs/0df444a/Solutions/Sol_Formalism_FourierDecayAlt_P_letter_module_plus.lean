-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.letter_module_plus
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:20.504855+00:00
-- url     : https://prove2.me/submissions/65b80588-4c62-419c-9b5f-70e4d168b95e

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondEmbedMulFirstEmbedApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_comm_RhE
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_rtt_RhE
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_rtt_mul_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_det_mul_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_detAt_RhE
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_comm_diag
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_RhE_herm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_herm_plus
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_eU_MU
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_diagScalar_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_diagScalar_conjTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_form_herm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_star_eU
import Theorems.Thm_Formalism_FourierDecayAlt_P_exchange_relation_plus


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
theorem _root_.solution : Formalism.FourierDecayAlt.Wd.LetterPlus := by
  intro K A S _ _ _ _ _ _ _ _ Ω RR TT q a Ya hM hRR hTT hYa hsYa
  have he : Wd4.MU (eU a : Fin 2 → Fin 2 → SlopeTestRemainingChoices S A) := Wd4.eU_MU a
  have hform : star (RR * ins a (TT Ya)) = RR * ins a (TT Ya) :=
    Wd4.form_herm hRR (hTT Ya) (hM.herm Ya hYa hsYa)
  have hc : ∀ Y Y' i j k l, Commute (TT Y i j) (Wd4.RhE (eU a) (Y' - Ya) k l) :=
    fun Y Y' i j k l => (Wd4.comm_RhE (Y' - Ya) (TT Y i j) (fun r s => hTT Y i j r s) k l).symm
  refine ⟨hform, ?_, ?_, ?_, ?_⟩
  · rintro Y ⟨hY, -⟩ hsY
    show (d0 (RR * ins a (TT Ya)) * (TT Y * Rh0 a (Y - Ya)))ᴴ =
      d0 (RR * ins a (TT Ya)) * (TT Y * Rh0 a (Y - Ya))
    rw [Wd4.diagScalar_mul]
    refine Wd4.herm_plus _ _ _ _ ?_ ?_ (hM.herm Y hY hsY) ?_ ?_ ?_
    · rw [Wd4.diagScalar_conjTranspose, hM.form_herm]
    · rw [← Wd4.diagScalar_mul, Wd4.diagScalar_conjTranspose, hform]
    · exact Wd4.RhE_herm (Wd1.star_eU a) (Y - Ya) (by rw [star_sub, hsY, hsYa])
    · exact Wd4.comm_diag _ RR (Wd4.comm_RhE (Y - Ya) RR hRR)
    · exact exchange_relation_plus K A S Ω RR TT q a Y Ya hM hTT hY hYa
  · rintro Y ⟨hY, -⟩ Y' ⟨hY', -⟩
    exact Wd4.rtt_mul_at TT (fun Y => Wd4.RhE (eU a) (Y - Ya)) Y Y' (hM.rtt Y hY Y' hY')
      (Wd4.rtt_RhE he Ya Y Y') hc
  · rintro Y ⟨hY, hY1⟩ ⟨hY', hY1'⟩
    exact Wd4.det_mul_at TT (fun Y => Wd4.RhE (eU a) (Y - Ya)) q _ Y (hM.det Y hY hY')
      (Wd4.detAt_RhE he Ya Y hY1 hY1') hc
  · intro Y hsY
    simp only [star_mul', star_div₀, star_add, star_sub, star_one, hsY, hsYa, hM.q_real Y hsY]
end Formalism.FourierDecayAlt.P
