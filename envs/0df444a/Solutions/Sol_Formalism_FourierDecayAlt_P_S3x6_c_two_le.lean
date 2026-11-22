-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x6.c_two_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:10:29.193985+00:00
-- url     : https://prove2.me/submissions/e2ac35c8-90d5-43e7-bc62-a251a58b3ccb

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
theorem _root_.solution (hq : Fintype.card K = q ^ 2) : 2 ≤ q := by
  have h1 : 1 < Fintype.card K := Fintype.one_lt_card
  rw [hq] at h1
  by_contra h
  interval_cases q <;> simp at h1
end Formalism.FourierDecayAlt.P.S3x6
