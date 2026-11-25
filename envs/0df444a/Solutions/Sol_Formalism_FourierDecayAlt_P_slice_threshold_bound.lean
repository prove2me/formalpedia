-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.slice_threshold_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:51:13.425381+00:00
-- url     : https://prove2.me/submissions/00a73fa5-c0e6-4e47-af23-4c84c76f086e

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerFourthCondition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C2.SliceThresholdBound := by
  intro c c₃ A a₁ r n hc3 hc3c hn hA ha
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hr : (0:ℝ) ≤ r := Nat.cast_nonneg r
  have hn3 : (n:ℝ) ≤ (n:ℝ) ^ 3 := by
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ n) (by linarith : (0:ℝ) ≤ n - 1))
      (by linarith : (0:ℝ) ≤ n + 1)]
  have h1 : (r:ℝ) * n + 1 ≤ ((r:ℝ) + 1) * A := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ r + 1) (by linarith : (0:ℝ) ≤ A - (n:ℝ) ^ 3),
      mul_nonneg (by linarith : (0:ℝ) ≤ r + 1) (by linarith : (0:ℝ) ≤ (n:ℝ) ^ 3 - n)]
  have h2 : 0 ≤ ((r:ℝ) + 1) ^ 2 := by positivity
  have h3 : 0 ≤ A := by nlinarith
  calc c₃ * ((r:ℝ) + 1) ^ 2 * ((r:ℝ) * n + 1) ≤ c₃ * ((r:ℝ) + 1) ^ 2 * (((r:ℝ) + 1) * A) :=
        mul_le_mul_of_nonneg_left h1 (mul_nonneg hc3 h2)
    _ = c₃ * ((r:ℝ) + 1) ^ 3 * A := by ring
    _ ≤ c * ((r:ℝ) + 1) ^ 3 * A :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc3c (by positivity)) h3
    _ ≤ a₁ := ha
end Formalism.FourierDecayAlt.P
