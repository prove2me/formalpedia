-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.levelExists
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:58:51.395875+00:00
-- url     : https://prove2.me/submissions/9c2cf92d-35c2-4741-a19a-f61df7b6ba38

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_levNab
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_levNabs
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_levPP
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_levP
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_levPb
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_levFns
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx2
variable {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Mx2
theorem _root_.solution : LevelExists := levelAssemble levFns levP levPb levPP levNab levNabs
end Formalism.FourierDecayAlt.P.Mx2
