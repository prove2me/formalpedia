-- Prove2me | solution 1 for Formalism.DegreeFormula.degreePowerSumMulEqZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:26:33.855948+00:00
-- url     : https://prove2.me/submissions/8e6062ea-b4e8-4966-a149-0d33dfa2eebc

import Definitions.Def_Formalism_DegreeFormula_FlagDegFormula
import Definitions.Def_Formalism_DegreeFormula_PointDegree_PermExpInj
import Definitions.Def_Formalism_DegreeFormula_PointDegree_PowSum
import Theorems.Thm_Formalism_DegreeFormula_PPowSum_degFlPowerSum

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
theorem _root_.solution : DegFlPowerSum := PPowSum.degFlPowerSum
end Formalism.DegreeFormula
