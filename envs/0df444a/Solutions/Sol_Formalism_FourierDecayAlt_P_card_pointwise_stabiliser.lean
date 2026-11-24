-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.card_pointwise_stabiliser
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:59:13.64623+00:00
-- url     : https://prove2.me/submissions/2197c74a-dbf8-4ea2-aa6c-d786bb7c43eb

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x1_nat_card_pointwise_stabiliser
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x1_card_isS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Formalism.FourierDecayAlt.P.S3x1
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S3.StabiliserIndexFinite := by
  intro K _ _ r k
  rw [card_isS, nat_card_pointwise_stabiliser, Nat.mul_assoc (Nat.card _) (_ ^ _) (_ ^ _), ← pow_add]
  congr 2
  rcases r with _ | r
  · simp
  · simp only [Nat.add_sub_cancel]
    ring
end Formalism.FourierDecayAlt.P
