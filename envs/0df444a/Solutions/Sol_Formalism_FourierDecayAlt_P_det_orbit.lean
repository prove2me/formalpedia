-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.det_orbit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:05:27.740801+00:00
-- url     : https://prove2.me/submissions/9ecc6599-1a31-4861-b37e-f45ac7b9ea8c

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Theorems.Thm_Formalism_FourierDecayAlt_P_G2_det_blk_col_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_G2_det_blk_row_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_G2_det_upper

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
theorem _root_.solution : Formalism.FourierDecayAlt.G.DetOrbit := by
  refine ⟨fun n t c p => ?_, fun d z v => ?_⟩
  · rw [Matrix.det_mul, Matrix.det_mul, lowRow, ptBlock, det_blk_col_zero, det_blk_col_zero,
      det_blk_row_zero, det_upper, Matrix.det_smul]
    simp; ring
  · rw [Matrix.det_mul, det_upper, ptLong, Matrix.det_smul]
    simp; ring
end Formalism.FourierDecayAlt.P
