-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.plane_wave_word_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:13:51.372917+00:00
-- url     : https://prove2.me/submissions/9a510be1-a8b2-443c-98ff-c08a645ac8bd

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_planeWaveWord

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
theorem _root_.solution : Formalism.FourierDecayAlt.Wd.PlaneWaveWord := by
  intro K A S _ _ _ _ _ _ _ _ QQ f fi s w hW hQ hw
  exact Wd11.planeWaveWord QQ f fi s w hW hQ hw
end Formalism.FourierDecayAlt.P
