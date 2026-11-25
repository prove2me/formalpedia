-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.jordan_holder_index
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:41:29.107386+00:00
-- url     : https://prove2.me/submissions/72e81f88-d801-410a-b673-d93ac0fed10d

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ReductionSurjective
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_red_surjective
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_JH_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.S3 Formalism.FourierDecayAlt.P.S3x2
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S3.IndexJH := by
  intro o _ _ _ r k L
  rw [JH_eq L, Subgroup.index_comap_of_surjective _ (red_surjective o _), Subgroup.index_mul_card]
end Formalism.FourierDecayAlt.P
