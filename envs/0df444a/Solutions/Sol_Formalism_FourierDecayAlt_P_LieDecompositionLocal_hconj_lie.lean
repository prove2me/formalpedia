-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LieDecompositionLocal.hconj_lie
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:58:16.175802+00:00
-- url     : https://prove2.me/submissions/b75ca78b-2b3b-4bce-9b26-8aaa551c0588

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_hpk_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_hpk_inv
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Qx2_hpk_sq__e1ad91698796


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
theorem _root_.solution {P : Mat k r} (hP : inLie k r P) : (Hpk k r)⁻¹ * Pᴴ * Hpk k r = -P := by
  unfold inLie at hP
  have hP' : Pᴴ * Hpk k r = -(Hpk k r * P) := eq_neg_of_add_eq_zero_left hP
  rw [Formalism.FourierDecayAlt.P.Qx2.hpk_inv, Matrix.mul_assoc, hP', Matrix.mul_neg, ← Matrix.mul_assoc,
    Formalism.FourierDecayAlt.P.Qx2.hpk_sq', Matrix.one_mul]
end Formalism.FourierDecayAlt.P.LieDecompositionLocal
