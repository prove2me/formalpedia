-- Prove2me | solution 1 for Formalism.CountingSumsFrames.detMulEqSumAdjugate_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:28:27.307267+00:00
-- url     : https://prove2.me/submissions/2cdf7c7c-1180-4a54-9855-73beab7246fb

import Definitions.Def_Formalism_PolynomialDimension_FrameSum
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FrobeniusDetVanishingHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Matrix
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution : DetMulEqSumAdjugate := by
  intro R _ r T s a
  have h : (T.adjugate *ᵥ (T *ᵥ s)) a = (T.det • s) a := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul]
    simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
  rw [Pi.smul_apply, smul_eq_mul] at h
  rw [← h]
  generalize T *ᵥ s = v
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _
end Formalism.CountingSumsFrames
