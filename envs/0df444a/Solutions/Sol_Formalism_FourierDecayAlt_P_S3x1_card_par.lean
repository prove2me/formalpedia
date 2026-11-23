-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x1.card_par
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:51:54.878344+00:00
-- url     : https://prove2.me/submissions/aba41e3e-ecdb-488a-b131-46acbd950d21

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x1_card_matrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x1_card_uni
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x1_parMap_bij

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
variable {A : Type} [CommRing A]
variable {r k : ℕ}
namespace Formalism.FourierDecayAlt.P.S3x1
theorem _root_.solution (K : Type) [Field K] [Fintype K] (r k : ℕ) (P : Matrix (Fin k) (Fin k) K → Prop) :
    Nat.card {x : Matrix (Idx r k) (Idx r k) K // Par P x} =
      Nat.card {h : Matrix (Fin k) (Fin k) K // P h} *
        Fintype.card K ^ (r * (r - 1) + 2 * r * (k + 1) + r ^ 2) := by
  rw [← Nat.card_congr (Equiv.ofBijective _ (parMap_bij (r := r) P))]
  simp only [Nat.card_prod]
  simp only [card_uni, card_matrix]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_sum, Fintype.card_unit]
  have h2 : r * (r - 1) / 2 + r * (r - 1) / 2 = r * (r - 1) := by
    have := Nat.div_mul_cancel (Nat.even_mul_pred_self r).two_dvd
    omega
  have : Fintype.card K ^ (r * (r - 1) + 2 * r * (k + 1) + r ^ 2) =
      Fintype.card K ^ (r * (r - 1) / 2) * Fintype.card K ^ (r * (r - 1) / 2) *
        (Fintype.card K ^ (r * (k + 1)) * (Fintype.card K ^ (r * r) * Fintype.card K ^ ((k + 1) * r))) := by
    rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, h2]
    congr 1
    ring
  rw [this]
  ring
end Formalism.FourierDecayAlt.P.S3x1
