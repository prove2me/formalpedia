-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3dx4.rpow_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:59:54.431295+00:00
-- url     : https://prove2.me/submissions/5806b998-c769-4423-a372-a900c79664fe

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CkOnZeroOfContOn
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbConvDDOfDecDD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped InnerProductSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3dx4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
namespace Formalism.FourierDecayAlt.P.S3dx4
theorem _root_.solution (t C a : ℝ) (ht : 0 ≤ t) (ha : a ≠ 0) : t ^ a * (C * t ^ (-a)) ≤ |C| := by
  rcases ht.lt_or_eq with h | h
  · rw [mul_left_comm, ← Real.rpow_add h, add_neg_cancel, Real.rpow_zero, mul_one]
    exact le_abs_self C
  · subst h
    rw [Real.zero_rpow ha, zero_mul]
    exact abs_nonneg C
end Formalism.FourierDecayAlt.P.S3dx4
