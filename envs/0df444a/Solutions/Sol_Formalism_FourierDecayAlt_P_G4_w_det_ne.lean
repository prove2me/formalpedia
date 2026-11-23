-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G4.w_det_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:18.58308+00:00
-- url     : https://prove2.me/submissions/6f0ab2f4-a0cb-4b3e-b3ad-e2efeecd39b5

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerBlockPoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_w_mul_w

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.FourierDecayAlt.G
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G4
namespace Formalism.FourierDecayAlt.P.G4
theorem _root_.solution (d : ℕ) : (wMat d).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (w_mul_w d)
  simp [Matrix.det_mul, h] at this
end Formalism.FourierDecayAlt.P.G4
