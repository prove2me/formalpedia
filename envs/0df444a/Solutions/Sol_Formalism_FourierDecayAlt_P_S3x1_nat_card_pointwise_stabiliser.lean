-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x1.nat_card_pointwise_stabiliser
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:56.793902+00:00
-- url     : https://prove2.me/submissions/febe3931-10b8-4180-915f-d12dad2d6c89

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x1_card_matrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x1_pointwise_stabiliser_parametrisation_bijective

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
    Nat.card {x : Matrix (Idx r k) (Idx r k) K // IsInertiaInfiniteCyclotomic x} =
      Nat.card {h : Matrix (Fin k) (Fin k) K // IsUnit h.det} *
        Fintype.card K ^ (r * k + r * r + k * r) := by
  rw [← Nat.card_congr (Equiv.ofBijective _ (pointwise_stabiliser_parametrisation_bijective (A := K) (r := r) (k := k)))]
  simp only [Nat.card_prod]
  simp only [card_matrix]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [pow_add, pow_add]
  ring
end Formalism.FourierDecayAlt.P.S3x1
