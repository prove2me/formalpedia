-- Prove2me | solution 1 for Formalism.GM.Top.smithZp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:34.38367+00:00
-- url     : https://prove2.me/submissions/2095e6b0-5d33-4791-8a03-1a50f13a739e

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GaussRad
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_MahlerK
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SmithZp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieRoots
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_DeterminantBlockLeadingTerm
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SmithBall
import Definitions.Def_Formalism_MahlerMeasure_FinalD
import Theorems.Thm_Formalism_GM_smith_form_p_adic_integers


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
theorem _root_.solution : SmithZp := smith_form_p_adic_integers
end Formalism.GM.Top
