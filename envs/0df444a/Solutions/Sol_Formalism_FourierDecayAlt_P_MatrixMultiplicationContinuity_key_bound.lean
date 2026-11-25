-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.key_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:06:57.995009+00:00
-- url     : https://prove2.me/submissions/f2a66e79-394e-4d14-9dc9-660abd274404

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousMulMt
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UhMeasurableSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SigmaContOn
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ReproducingFormulaReduction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
noncomputable section
set_option maxHeartbeats 1600000
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity
open Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity
theorem _root_.solution {A S X Y a : ℝ} (hA : 1 ≤ A) (hX : 1 ≤ X) (hY : 1 ≤ Y) (hS0 : 0 < S) (ha : 0 < a)
    (hS : S ≤ A * X * Y) : Y ^ (-a) * A ^ (-a) ≤ X ^ (a / 2) * (Y ^ (-(a / 2)) * S ^ (-(a / 2))) := by
  have hA0 : 0 < A := by linarith
  have hX0 : 0 < X := by linarith
  have hY0 : 0 < Y := by linarith
  have y1 : 0 < Y ^ (-a) := Real.rpow_pos_of_pos hY0 _
  have a1 : 0 < A ^ (-a) := Real.rpow_pos_of_pos hA0 _
  have x2 : 0 < X ^ (a / 2) := Real.rpow_pos_of_pos hX0 _
  have y2 : 0 < Y ^ (-(a / 2)) := Real.rpow_pos_of_pos hY0 _
  have s2 : 0 < S ^ (-(a / 2)) := Real.rpow_pos_of_pos hS0 _
  have h1 : Real.log S ≤ Real.log A + Real.log X + Real.log Y := by
    have e1 : Real.log (A * X * Y) = Real.log A + Real.log X + Real.log Y := by
      rw [Real.log_mul (mul_pos hA0 hX0).ne' hY0.ne', Real.log_mul hA0.ne' hX0.ne']
    rw [← e1]
    exact Real.log_le_log hS0 hS
  have h2 : 0 ≤ Real.log A := Real.log_nonneg hA
  rw [← Real.log_le_log_iff (mul_pos y1 a1) (mul_pos x2 (mul_pos y2 s2)),
    Real.log_mul y1.ne' a1.ne', Real.log_mul x2.ne' (mul_pos y2 s2).ne', Real.log_mul y2.ne' s2.ne',
    Real.log_rpow hY0, Real.log_rpow hA0, Real.log_rpow hX0, Real.log_rpow hY0, Real.log_rpow hS0]
  nlinarith [mul_le_mul_of_nonneg_left h1 ha.le, mul_nonneg ha.le h2]
end Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity
