-- Prove2me | solution 1 for Formalism.HermiteSiegelSlopes.infinitePlace_liesOver_comap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:09.073179+00:00
-- url     : https://prove2.me/submissions/867a5fc1-4c02-44c9-bb4b-f568da93de9a

import Definitions.Def_Formalism_MonomialMeanResidues_FilteredDegree
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_MonomialMeanResidues_MonomialMeanProofs_SpanEqTopAndRankOfLinearIndependent

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
theorem _root_.solution (w : InfinitePlace E) : w.LiesOver (w.comap (algebraMap F E)) := by
  first
    | exact inferInstance
    | exact ⟨rfl⟩
end Formalism.HermiteSiegelSlopes
