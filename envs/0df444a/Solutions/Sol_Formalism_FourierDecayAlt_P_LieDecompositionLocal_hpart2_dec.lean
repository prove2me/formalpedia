-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LieDecompositionLocal.hpart2_dec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:18:28.186804+00:00
-- url     : https://prove2.me/submissions/b709d61a-cd3f-469a-a8f8-4495058d9a7d

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
    hpart2 (Hpk k r) (P + Complex.I • Q) = Q := by
  unfold hpart2
  rw [conjTranspose_add, conjTranspose_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, hconj_lie hP, hconj_lie hQ]
  simp only [RCLike.star_def, Complex.conj_I]
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.neg_apply, smul_eq_mul]
  field_simp
  ring_nf
  try simp [Complex.I_sq]
  try ring
end Formalism.FourierDecayAlt.P.LieDecompositionLocal
