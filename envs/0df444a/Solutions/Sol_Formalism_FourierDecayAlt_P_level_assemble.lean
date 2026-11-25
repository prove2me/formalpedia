-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.level_assemble
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:42:50.980214+00:00
-- url     : https://prove2.me/submissions/2c2c88d3-f4ab-4449-9d8b-dedc8058b5ad

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_levelAssemble

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.M.LevelAssemble := Mx2.levelAssemble
end Formalism.FourierDecayAlt.P
