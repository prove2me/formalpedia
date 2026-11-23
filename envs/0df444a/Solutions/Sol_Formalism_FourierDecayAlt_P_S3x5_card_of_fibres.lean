-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x5.card_of_fibres
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:57.246057+00:00
-- url     : https://prove2.me/submissions/18bf724e-f393-41c0-b06c-023d2588c122

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFrameCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x5
open Matrix Formalism.FourierDecayAlt.S3
namespace Formalism.FourierDecayAlt.P.S3x5
theorem _root_.solution {P A : Type} [Finite P] [Finite A] (f : P → A) (m : ℝ)
    (h : ∀ a, (Nat.card {p // f p = a} : ℝ) = m) : (Nat.card P : ℝ) = Nat.card A * m := by
  classical
  have := Fintype.ofFinite A
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
  push_cast
  rw [Finset.sum_congr rfl (fun a _ => h a), Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.card_eq_fintype_card]
end Formalism.FourierDecayAlt.P.S3x5
