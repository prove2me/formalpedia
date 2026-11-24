-- Prove2me | solution 1 for Formalism.GM.Top.lieRoots
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:11.966923+00:00
-- url     : https://prove2.me/submissions/a09822c0-42e1-4ae5-9597-9da43020d33c

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GaussRad
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_MahlerK
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SmithZp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieRoots
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_DeterminantBlockLeadingTerm
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SmithBall
import Definitions.Def_Formalism_MahlerMeasure_FinalD
import Theorems.Thm_Formalism_GM_gauss_norm_multiplicative
import Theorems.Thm_Formalism_GM_lieRoots_of


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
theorem _root_.solution : LieRoots := lieRoots_of gauss_norm_multiplicative
end Formalism.GM.Top
