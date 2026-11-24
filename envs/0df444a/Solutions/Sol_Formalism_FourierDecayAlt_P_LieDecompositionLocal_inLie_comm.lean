-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LieDecompositionLocal.inLie_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:49:49.113888+00:00
-- url     : https://prove2.me/submissions/792679d0-d7f9-498f-b617-da2e8ada8904

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LieDecompositionLocal
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.LieDecompositionLocal
theorem _root_.solution {X Y : Mat k r} (hX : inLie k r X) (hY : inLie k r Y) : inLie k r (X * Y - Y * X) := by
  unfold inLie at *
  have hX' : Xᴴ * Hpk k r = -(Hpk k r * X) := eq_neg_of_add_eq_zero_left hX
  have hY' : Yᴴ * Hpk k r = -(Hpk k r * Y) := eq_neg_of_add_eq_zero_left hY
  rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, Matrix.sub_mul, Matrix.mul_assoc,
    Matrix.mul_assoc Xᴴ, hX', hY', Matrix.mul_neg, Matrix.mul_neg, ← Matrix.mul_assoc Yᴴ,
    ← Matrix.mul_assoc Xᴴ, hY', hX']
  noncomm_ring
end Formalism.FourierDecayAlt.P.LieDecompositionLocal
