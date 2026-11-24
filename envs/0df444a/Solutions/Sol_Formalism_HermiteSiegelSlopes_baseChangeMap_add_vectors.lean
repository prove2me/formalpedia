-- Prove2me | solution 1 for Formalism.HermiteSiegelSlopes.baseChangeMap_add_vectors
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:04.105382+00:00
-- url     : https://prove2.me/submissions/4ba1ad5c-8e46-46d3-9c52-056437155f89

import Definitions.Def_Formalism_MonomialMeanResidues_FilteredDegree
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_MonomialMeanResidues_MonomialMeanProofs_SpanEqTopAndRankOfLinearIndependent
import Theorems.Thm_Formalism_HermiteSiegelSlopes_baseChangeMap_map_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Finset
noncomputable section
open Formalism Formalism.HermiteSiegelSlopes
open Formalism.HN
open scoped nonZeroDivisors
open IsDedekindDomain
variable {F E ι : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace Formalism.HermiteSiegelSlopes
theorem _root_.solution (x y : ι → F) : bcMap (E := E) (x + y) = bcMap x + bcMap y := by
  exact baseChangeMap_map_add x y
end Formalism.HermiteSiegelSlopes
