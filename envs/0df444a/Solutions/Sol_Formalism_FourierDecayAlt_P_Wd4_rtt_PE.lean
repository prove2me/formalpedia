-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd4.rtt_PE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:53:05.080625+00:00
-- url     : https://prove2.me/submissions/81654c41-b1c5-4b60-845f-148087100db7

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondEmbedMulFirstEmbedApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_firstEmbed_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_eval_two_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_kronecker_E1_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_eval_two_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_swap_mul_firstEmbed
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_swap_mul_secondEmbed
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_PE_first_mul_second_eq_swap
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_PE_second_mul_first_eq_swap
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_ybe_alg
import Theorems.Thm_Formalism_FourierDecayAlt_P_W_entries_mem_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_W_first_embedding_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd4
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.W
variable {K B : Type} [Field K] [Ring B] [Algebra K B]
variable {e : Fin 2 → Fin 2 → B}
namespace Formalism.FourierDecayAlt.P.Wd4
theorem _root_.solution (he : MU e) (u v : K) :
    ((u - v) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) - Pf B) * E1 (u • (1 : M2 B) - PE e) *
        E2 (v • (1 : M2 B) - PE e) =
      E2 (v • (1 : M2 B) - PE e) * E1 (u • (1 : M2 B) - PE e) *
        ((u - v) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) - Pf B) := by
  rw [firstEmbed_sub, kronecker_E1_smul, first_embedding_one, eval_two_sub, eval_two_smul, entries_mem_one]
  exact ybe_alg _ _ _ u v (PE_first_mul_second_eq_swap he) (swap_mul_firstEmbed _).symm (PE_second_mul_first_eq_swap he) (swap_mul_secondEmbed _).symm
end Formalism.FourierDecayAlt.P.Wd4
