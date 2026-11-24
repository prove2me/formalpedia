-- Prove2me | solution 1 for Formalism.GM.Top.lieMat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:03:07.933659+00:00
-- url     : https://prove2.me/submissions/77053253-29c5-43f9-b12f-51e032be63e1

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GaussRad
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_MahlerK
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SmithZp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieRoots
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_DeterminantBlockLeadingTerm
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SmithBall
import Definitions.Def_Formalism_MahlerMeasure_FinalD
import Theorems.Thm_Formalism_GM_lieMat_of
import Theorems.Thm_Formalism_GM_mahler_binomial_unit_ball


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.Top
open Formalism.GM
namespace Formalism.GM.Top
theorem _root_.solution : LieMat := lieMat_of mahler_binomial_unit_ball
end Formalism.GM.Top
