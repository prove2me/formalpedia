-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x3.card_S
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:57:00.774795+00:00
-- url     : https://prove2.me/submissions/ff62d739-ace6-42e4-a647-d53740617b40

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemIntegralGlOfMiddleBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_card_prod_set

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x3
open Matrix Formalism.FourierDecayAlt.S3
open Formalism.DoubleCosetMeasures (IsUpUni upUniG)
variable {A : Type} [CommRing A] {r k : ℕ}
namespace Formalism.FourierDecayAlt.P.S3x3
theorem _root_.solution : Nat.card {x : Matrix (Idx r k) (Idx r k) A // IsS x} =
    Nat.card (GL (Fin k) A) * Nat.card {x : Matrix (Idx r k) (Idx r k) A // IsN x} := by
  have h := card_prod_set (r := r) (fun h : Matrix (Fin k) (Fin k) A => IsUnit h.det) (fun _ h => h)
  have h2 : Nat.card {g : GL (Fin k) A // IsUnit (g : Matrix (Fin k) (Fin k) A).det} =
      Nat.card (GL (Fin k) A) :=
    Nat.card_congr (Equiv.subtypeUnivEquiv fun g => (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit)
  rw [h2] at h
  exact h
end Formalism.FourierDecayAlt.P.S3x3
