-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz5.top_alg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:17.034747+00:00
-- url     : https://prove2.me/submissions/454ad355-44f3-4117-8bde-6a26fcba073e

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CriticalThresholdLowerBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz5
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz5
theorem _root_.solution (n : ℕ) (κ e B a b K θ E W : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hθ : θ ≠ 0) :
    (κ * e / θ * B / (a * b / K)) ^ (n + 2) * ((a ^ n * (a + b)) * ((E ^ (n + 1) * W) * (b * θ) ^ n)) =
      (e ^ (n + 2) * B) * (K ^ 2 * (a + b) / (a ^ 2 * b ^ 2)) * (1 / θ ^ 2) *
        (κ ^ (n + 2) * K ^ n * E ^ (n + 1)) * (W * B ^ (n + 1)) := by
  have h1 : (a * a⁻¹) ^ n = 1 := by rw [mul_inv_cancel₀ ha, one_pow]
  have h2 : (b * b⁻¹) ^ n = 1 := by rw [mul_inv_cancel₀ hb, one_pow]
  have h3 : (θ * θ⁻¹) ^ n = 1 := by rw [mul_inv_cancel₀ hθ, one_pow]
  rw [div_div_eq_mul_div]
  linear_combination
    ((e ^ (n + 2) * B) * (K ^ 2 * (a + b) / (a ^ 2 * b ^ 2)) * (1 / θ ^ 2) *
      (κ ^ (n + 2) * K ^ n * E ^ (n + 1)) * (W * B ^ (n + 1)) * (b * b⁻¹) ^ n * (θ * θ⁻¹) ^ n) * h1 +
    ((e ^ (n + 2) * B) * (K ^ 2 * (a + b) / (a ^ 2 * b ^ 2)) * (1 / θ ^ 2) *
      (κ ^ (n + 2) * K ^ n * E ^ (n + 1)) * (W * B ^ (n + 1)) * (θ * θ⁻¹) ^ n) * h2 +
    ((e ^ (n + 2) * B) * (K ^ 2 * (a + b) / (a ^ 2 * b ^ 2)) * (1 / θ ^ 2) *
      (κ ^ (n + 2) * K ^ n * E ^ (n + 1)) * (W * B ^ (n + 1))) * h3
end Formalism.FourierDecayAlt.P.Sz5
