-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LieDecompositionLocal.hpart1_dec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:18:27.277737+00:00
-- url     : https://prove2.me/submissions/4f623344-4b6b-448c-bb70-b00aa21e2322

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_hconj_lie

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
theorem _root_.solution {P Q : Mat k r} (hP : inLie k r P) (hQ : inLie k r Q) :
    hpart1 (Hpk k r) (P + Complex.I • Q) = P := by
  unfold hpart1
  rw [conjTranspose_add, conjTranspose_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, hconj_lie hP, hconj_lie hQ]
  simp only [RCLike.star_def, Complex.conj_I]
  ext i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.neg_apply, smul_eq_mul]
  ring
end Formalism.FourierDecayAlt.P.LieDecompositionLocal
