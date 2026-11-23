-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x1.card_isS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:59:24.334667+00:00
-- url     : https://prove2.me/submissions/c3a2cbcb-cefd-4f0a-91ae-ace6289dc693

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x1_card_par

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x1
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det)
open Formalism.FourierDecayAlt.S3
variable {A : Type} [CommRing A] {r k : ℕ}
namespace Formalism.FourierDecayAlt.P.S3x1
theorem _root_.solution (K : Type) [Field K] [Fintype K] (r k : ℕ) :
    Nat.card {x : Matrix (Idx r k) (Idx r k) K // IsS x} =
      Nat.card {h : Matrix (Fin k) (Fin k) K // IsUnit h.det} *
        Fintype.card K ^ (r * (r - 1) + 2 * r * (k + 1) + r ^ 2) := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight isS_iff), card_par]
end Formalism.FourierDecayAlt.P.S3x1
