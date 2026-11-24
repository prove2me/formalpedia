-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd4.rtt_QE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:03.11691+00:00
-- url     : https://prove2.me/submissions/58eda05e-0f93-4ffb-ad51-ba56d46f63ce

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_QE_first_mul_second_eq_swap
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_QE_second_mul_first_eq_swap
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_ybet_alg
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
theorem _root_.solution (he : MU e) (d' d : K) :
    ((d - d') • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) - Pf B) * E1 (d' • (1 : M2 B) - QE e) *
        E2 (d • (1 : M2 B) - QE e) =
      E2 (d • (1 : M2 B) - QE e) * E1 (d' • (1 : M2 B) - QE e) *
        ((d - d') • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) - Pf B) := by
  rw [firstEmbed_sub, kronecker_E1_smul, first_embedding_one, eval_two_sub, eval_two_smul, entries_mem_one]
  exact ybet_alg _ _ _ d' d (swap_mul_firstEmbed _) (swap_mul_secondEmbed _) (QE_first_mul_second_eq_swap he) (QE_second_mul_first_eq_swap he)
end Formalism.FourierDecayAlt.P.Wd4
