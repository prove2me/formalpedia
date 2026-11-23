-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G4.w_mul_w
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:45:16.416641+00:00
-- url     : https://prove2.me/submissions/31211f4c-2f93-48d2-a569-682a45d30b37

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerBlockPoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_w_mul_apply

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
theorem _root_.solution (d : ℕ) : wMat d * wMat d = 1 := by
  ext i j
  rw [w_mul_apply]
  simp [wMat, Matrix.one_apply, eq_comm]
end Formalism.FourierDecayAlt.P.G4
