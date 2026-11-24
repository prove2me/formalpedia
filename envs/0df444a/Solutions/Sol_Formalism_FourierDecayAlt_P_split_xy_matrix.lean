-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.split_xy_matrix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:25.656268+00:00
-- url     : https://prove2.me/submissions/18ef9b3c-c820-4b56-b74d-cc888166cba3

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakApproximationGL
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakApproximationGL_xOf_redOf
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakApproximationGL_matrix_redOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.WeakApproximationGL
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.SplitXYMatrix :=
  fun m t ρ₁ p => ⟨xOf_redOf m p, matrix_redOf m t ρ₁ p⟩
end Formalism.FourierDecayAlt.P
