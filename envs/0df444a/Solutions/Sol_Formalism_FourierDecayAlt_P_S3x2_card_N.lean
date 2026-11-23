-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x2.card_N
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:49:59.7649+00:00
-- url     : https://prove2.me/submissions/2398164d-67e8-45fb-8e3b-5fb3693f42f7

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ReductionSurjective
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_card_of_subgroupSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_isN_set

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x2
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.S3
variable {A : Type} [CommRing A] {r k : ℕ}
namespace Formalism.FourierDecayAlt.P.S3x2
theorem _root_.solution : Nat.card {x : Matrix (Idx r k) (Idx r k) A // IsN x} = Nat.card (UcG A (cI r k)) :=
  card_of_subgroupSet _ _ isN_set
end Formalism.FourierDecayAlt.P.S3x2
