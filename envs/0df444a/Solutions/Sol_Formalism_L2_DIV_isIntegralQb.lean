-- Prove2me | solution 1 for Formalism.L2.DIV.isIntegralQb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:34:12.715271+00:00
-- url     : https://prove2.me/submissions/761e0dce-4427-4e92-aadf-0a774d4e36ee

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ConjugationAtDistinguishedPlace
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_PowValCast
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoeffLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.L2.Host Formalism.DivisionValues
namespace Formalism.L2.DIV
theorem _root_.solution (x : Qb) : IsIntegral ℚ x := ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic x).isIntegral
end Formalism.L2.DIV
