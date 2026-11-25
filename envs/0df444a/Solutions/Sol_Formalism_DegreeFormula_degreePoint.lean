-- Prove2me | solution 1 for Formalism.DegreeFormula.degreePoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:26:32.499872+00:00
-- url     : https://prove2.me/submissions/b6c89001-3a72-4fbd-8b71-7c29fe6e7111

import Definitions.Def_Formalism_DegreeFormula_FlagDegFormula
import Definitions.Def_Formalism_DegreeFormula_PointDegree_PermExpInj
import Theorems.Thm_Formalism_DegreeFormula_PermutationPointDegree_degFlPoint

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
theorem _root_.solution : DegFlPoint := Formalism.DegreeFormula.PermutationPointDegree.degFlPoint
end Formalism.DegreeFormula
