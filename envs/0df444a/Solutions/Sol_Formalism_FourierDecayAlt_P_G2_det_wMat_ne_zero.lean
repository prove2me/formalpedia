-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G2.det_wMat_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:43:48.345722+00:00
-- url     : https://prove2.me/submissions/abb19690-4366-4004-a2b5-bff3b24055d2

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Theorems.Thm_Formalism_FourierDecayAlt_P_G2_det_wMat_succ

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G2
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.G2
theorem _root_.solution (n : ℕ) : (wMat n).det ≠ 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [det_wMat_succ]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) ih
end Formalism.FourierDecayAlt.P.G2
