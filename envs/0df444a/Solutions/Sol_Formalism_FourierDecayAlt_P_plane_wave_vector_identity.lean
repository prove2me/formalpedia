-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.plane_wave_vector_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:51:36.637449+00:00
-- url     : https://prove2.me/submissions/b9faaea9-4c41-4dd1-b9e7-fdcda2ca57e7

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_planeWaveVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Wd.PlaneWaveVec := by
  intro K A S _ _ _ _ _ _ _ _ σ f fi s w hW hc hci hp hw
  exact Wd11.planeWaveVec σ f fi s w hW hc hci hp hw
end Formalism.FourierDecayAlt.P
