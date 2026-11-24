-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.cofactor_leading_minor_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:41:31.5078+00:00
-- url     : https://prove2.me/submissions/00446853-07b6-4e87-9207-2e92bbd338e2

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_CohomologicalDescent_LD_cofactor_leading_minor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LA
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution {r s t : ℕ} (h : s + t = r) :
    genericDet ℤ r * cofMap r (leadingMinorPolynomial r s) = genericDet ℤ r ^ s * leadingMinorPolynomial r t := by
  unfold leadingMinorPolynomial
  rw [dif_pos (by omega), dif_pos (by omega)]
  exact cofactor_leading_minor h _ _
end Formalism.CohomologicalDescent.LD
