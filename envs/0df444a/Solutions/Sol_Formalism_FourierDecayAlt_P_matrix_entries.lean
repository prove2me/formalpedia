-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.matrix_entries
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:14.087912+00:00
-- url     : https://prove2.me/submissions/36f9ed29-f3b4-4435-8214-af441a842211

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Theorems.Thm_Formalism_FourierDecayAlt_P_G2_blk_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.EntriesM := by
  intro n t c p
  obtain ⟨a, v, b⟩ := p
  simp only [lowRow, ptBlock, Mcoord, blk_mul, Xof, rhoOf, upper]
  congr 1
  · simp [Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul, smul_add]
  · ext i; simp [Matrix.mulVec_smul, Matrix.smul_mulVec]
  · simp [Matrix.vecMul_smul, Matrix.mul_add, Matrix.vecMul_add, smul_add, Matrix.smul_vecMul,
      ← Matrix.vecMul_vecMul]
  · simp [Matrix.mulVec_smul, Matrix.vecMul_smul, Matrix.dotProduct_mulVec, add_comm]
end Formalism.FourierDecayAlt.P
