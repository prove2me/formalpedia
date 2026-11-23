-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x6.c_pow_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:02:30.008774+00:00
-- url     : https://prove2.me/submissions/ad146434-f24a-424e-8f4e-4519eb3e5548

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictOrthogonalComplementNondeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x6
open Module
variable {K : Type} [Field K] {σ : K →+* K}
open Finset
variable (K : Type) [Field K] [Fintype K] (q : ℕ)
namespace Formalism.FourierDecayAlt.P.S3x6
theorem _root_.solution (hq : Fintype.card K = q ^ 2) (x : K) : (x ^ q) ^ q = x := by
  rw [← pow_mul, ← sq, ← hq, FiniteField.pow_card]
end Formalism.FourierDecayAlt.P.S3x6
