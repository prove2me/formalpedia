-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x6.card_norm_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:03:43.746799+00:00
-- url     : https://prove2.me/submissions/cbfa5509-4b4e-4407-bd49-0edbe910b951

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictOrthogonalComplementNondeg
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_c_count

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
theorem _root_.solution (hq : Fintype.card K = q ^ 2) (n : ℕ) :
    (q : ℤ) * Nat.card {w : Fin n → K // ∑ i, (w i) ^ q * w i = 1} = q ^ n * (q ^ n - (-1) ^ n) := by
  classical
  have h := c_count K q hq n 1 (one_pow q)
  rw [if_neg one_ne_zero] at h
  rw [← h, Nat.card_eq_fintype_card, Fintype.card_subtype]
end Formalism.FourierDecayAlt.P.S3x6
