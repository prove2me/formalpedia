-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz1.colIdx_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:02.189703+00:00
-- url     : https://prove2.me/submissions/04a68ed2-0968-44d0-b80a-76dd81c93b98

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz1_glCard_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz1
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz1
theorem _root_.solution (k : ℕ) (q : ℝ) (hq : 1 < q) : colIdx k q ≠ 0 := by
  have hq0 : q ≠ 0 := by linarith
  unfold colIdx
  exact div_ne_zero (glCard_ne_zero k q hq) (pow_ne_zero _ hq0)
end Formalism.FourierDecayAlt.P.Sz1
