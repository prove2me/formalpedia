-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.pow_sub_one_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:34:14.923974+00:00
-- url     : https://prove2.me/submissions/95f878a5-c8fe-4802-acb0-705dcedd4bbd

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.B4
theorem _root_.solution {t : ℝ} (h0 : 0 ≤ t) (h2 : t ≤ 2) (n : ℕ) : |t ^ n - 1| ≤ (2 ^ n - 1) * |t - 1| := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : t ^ (n + 1) - 1 = t * (t ^ n - 1) + (t - 1) := by ring
    calc |t ^ (n + 1) - 1| ≤ |t * (t ^ n - 1)| + |t - 1| := by rw [e]; exact abs_add_le _ _
      _ = t * |t ^ n - 1| + |t - 1| := by rw [abs_mul, abs_of_nonneg h0]
      _ ≤ 2 * ((2 ^ n - 1) * |t - 1|) + |t - 1| := by
          have := mul_le_mul h2 ih (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
          linarith
      _ = (2 ^ (n + 1) - 1) * |t - 1| := by ring
end Formalism.FourierDecayAlt.P.B4
