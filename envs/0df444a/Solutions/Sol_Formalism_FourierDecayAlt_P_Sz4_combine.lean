-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz4.combine
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:39:39.254241+00:00
-- url     : https://prove2.me/submissions/5980b24b-bb88-4a7f-bbe9-7546de048e45

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz4
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz4
theorem _root_.solution (E E' C R R' W α β γ M : ℝ) (hE : 0 < E) (hE' : 0 < E') (hC : 0 < C) (hW : 0 < W)
    (hβ : 0 < β) (hM : 0 < M) (h1 : E' ≤ α * E) (h2 : R' ≤ β) (h3 : γ ≤ R)
    (h4 : α * β ≤ M * γ) : E' * C * (R' * W) ≤ M * (E * C * (R * W)) := by
  have a1 : E' * R' ≤ E' * β := mul_le_mul_of_nonneg_left h2 hE'.le
  have a2 : E' * β ≤ α * E * β := mul_le_mul_of_nonneg_right h1 hβ.le
  have a3 : α * β * E ≤ M * γ * E := mul_le_mul_of_nonneg_right h4 hE.le
  have a4 : M * E * γ ≤ M * E * R := mul_le_mul_of_nonneg_left h3 (mul_pos hM hE).le
  have a5 : E' * R' ≤ M * E * R := by nlinarith
  have a6 : E' * R' * (C * W) ≤ M * E * R * (C * W) :=
    mul_le_mul_of_nonneg_right a5 (mul_pos hC hW).le
  nlinarith
end Formalism.FourierDecayAlt.P.Sz4
