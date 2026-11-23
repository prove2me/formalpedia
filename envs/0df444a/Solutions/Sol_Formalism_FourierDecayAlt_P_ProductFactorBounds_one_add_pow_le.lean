-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ProductFactorBounds.one_add_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:40:11.713694+00:00
-- url     : https://prove2.me/submissions/0c305205-2ec4-41d3-883e-8b0dbc48a220

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ProductFactorBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ProductFactorBounds
open Formalism.FourierDecayAlt.F7
namespace Formalism.FourierDecayAlt.P.ProductFactorBounds
theorem _root_.solution (u : ℝ) (hu : 0 ≤ u) (k : ℕ) (hk : (k : ℝ) * u ≤ 1) :
    (1 + u) ^ k ≤ 1 + k * u + (k * u) ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk' : (k : ℝ) * u ≤ 1 := by
      push_cast at hk; nlinarith
    have h := ih hk'
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    rw [pow_succ]
    push_cast
    have h1 : (1 + u) ^ k * (1 + u) ≤ (1 + k * u + (k * u) ^ 2) * (1 + u) :=
      mul_le_mul_of_nonneg_right h (by linarith)
    have h2 : (k : ℝ) * u * (k * u ^ 2) ≤ 1 * (k * u ^ 2) :=
      mul_le_mul_of_nonneg_right hk' (by positivity)
    nlinarith [sq_nonneg u]
end Formalism.FourierDecayAlt.P.ProductFactorBounds
