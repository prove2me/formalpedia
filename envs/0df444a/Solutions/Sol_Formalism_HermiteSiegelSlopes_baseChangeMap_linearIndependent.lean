-- Prove2me | solution 1 for Formalism.HermiteSiegelSlopes.baseChangeMap_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:04.343708+00:00
-- url     : https://prove2.me/submissions/17902c85-f730-4a23-bdfb-9fe13d7767e6

import Definitions.Def_Formalism_MonomialMeanResidues_FilteredDegree
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_MonomialMeanResidues_MonomialMeanProofs_SpanEqTopAndRankOfLinearIndependent
import Theorems.Thm_Formalism_HermiteSiegelSlopes_bc_linIndep

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
  [Fintype ι] [DecidableEq ι]
namespace Formalism.HermiteSiegelSlopes
theorem _root_.solution {j : ℕ} (e : Fin j → ι → F) (he : LinearIndependent F e) :
    LinearIndependent E (fun a => bcMap (E := E) (e a)) := by
  exact bc_linIndep e he
end Formalism.HermiteSiegelSlopes
