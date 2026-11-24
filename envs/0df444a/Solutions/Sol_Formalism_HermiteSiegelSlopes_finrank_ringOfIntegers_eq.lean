-- Prove2me | solution 1 for Formalism.HermiteSiegelSlopes.finrank_ringOfIntegers_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:06.765744+00:00
-- url     : https://prove2.me/submissions/58061cce-94dc-4cf6-b29c-dcc22903f479

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
theorem _root_.solution : finrank (𝓞 F) (𝓞 E) = finrank F E :=
  (IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E).symm
end Formalism.HermiteSiegelSlopes
