-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.det_weyl_matrix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:45:25.93164+00:00
-- url     : https://prove2.me/submissions/2797bdd1-5f34-4014-b38f-c2df516e70bf

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Theorems.Thm_Formalism_FourierDecayAlt_P_G2_det_wMat_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_G2_det_wMat_ne_zero

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
theorem _root_.solution : Formalism.FourierDecayAlt.G.DetMatch :=
  fun n => ⟨det_wMat_succ n, det_wMat_ne_zero n⟩
end Formalism.FourierDecayAlt.P
