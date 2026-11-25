-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux5.det_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:07:12.472837+00:00
-- url     : https://prove2.me/submissions/f9ac47cc-cd52-416d-a8e7-21027f31fb2f

import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qi39_det_norm_le__ef491038fe38
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetNormLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux5
namespace Formalism.FourierDecayAlt.P.Ux5
theorem _root_.solution {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) {m : ℝ} (h : EB A m) :
    ‖A.det‖ ≤ (Fintype.card n).factorial * m ^ Fintype.card n := by
  first | exact P2M_UpperTheory_Reformulated_B_Qi39_det_norm_le__ef491038fe38 .. | (apply P2M_UpperTheory_Reformulated_B_Qi39_det_norm_le__ef491038fe38 <;> assumption) | (intros; apply P2M_UpperTheory_Reformulated_B_Qi39_det_norm_le__ef491038fe38 <;> assumption) | (apply @P2M_UpperTheory_Reformulated_B_Qi39_det_norm_le__ef491038fe38 <;> assumption) | (intros; apply @P2M_UpperTheory_Reformulated_B_Qi39_det_norm_le__ef491038fe38 <;> assumption) | (apply @P2M_UpperTheory_Reformulated_B_Qi39_det_norm_le__ef491038fe38 <;> first | assumption | infer_instance) | exact @P2M_UpperTheory_Reformulated_B_Qi39_det_norm_le__ef491038fe38 n ‹_› ‹_› A m h | exact @P2M_UpperTheory_Reformulated_B_Qi39_det_norm_le__ef491038fe38 n ‹_› ‹_› A m | exact @P2M_UpperTheory_Reformulated_B_Qi39_det_norm_le__ef491038fe38 n ‹_› ‹_› A | exact @P2M_UpperTheory_Reformulated_B_Qi39_det_norm_le__ef491038fe38 n ‹_› ‹_› | exact @P2M_UpperTheory_Reformulated_B_Qi39_det_norm_le__ef491038fe38 n ‹_› | exact @P2M_UpperTheory_Reformulated_B_Qi39_det_norm_le__ef491038fe38 n
end Formalism.FourierDecayAlt.P.Ux5
