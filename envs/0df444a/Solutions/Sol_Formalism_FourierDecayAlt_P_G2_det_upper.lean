-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G2.det_upper
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:20:09.974811+00:00
-- url     : https://prove2.me/submissions/3348d8d2-26f6-419c-86ea-03eb6827028f

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi

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
theorem _root_.solution {d : ℕ} (v : UT d → ℂ) : (upper v).det = 1 := by
  have h : (upper v).BlockTriangular id := by
    intro i j hij
    have hij' : j < i := hij
    simp [upper, strictUpper, Matrix.one_apply, hij'.ne', not_lt.2 hij'.le]
  rw [Matrix.det_of_isUpperTriangular h]
  simp [upper, strictUpper]
end Formalism.FourierDecayAlt.P.G2
