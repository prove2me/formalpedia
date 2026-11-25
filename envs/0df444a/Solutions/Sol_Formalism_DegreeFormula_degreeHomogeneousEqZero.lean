-- Prove2me | solution 1 for Formalism.DegreeFormula.degreeHomogeneousEqZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:32:56.736441+00:00
-- url     : https://prove2.me/submissions/7c7298f9-bd14-4666-a711-592b8bb422d1

import Definitions.Def_Formalism_DegreeFormula_FlagDegFormula
import Definitions.Def_Formalism_DegreeFormula_PointDegree_PermExpInj
import Definitions.Def_Formalism_DegreeFormula_PointDegree_PowSum
import Theorems.Thm_Formalism_DegreeFormula_PPowSum_degFlHomog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.DegreeFormula
namespace Formalism.DegreeFormula
theorem _root_.solution : DegFlHomog := PPowSum.degFlHomog
end Formalism.DegreeFormula
