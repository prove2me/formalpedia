-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.exp_le_cast_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:27:19.245372+00:00
-- url     : https://prove2.me/submissions/646ae4ed-c9b9-4ce5-a1f1-002b99f717a5

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors

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
theorem _root_.solution (l : ℕ) {r r' : ℕ} (h : r' = r) (ν μ : Fin r → ℕ) (e : ℕ) :
    ExpLe l r' (fun a => ν (Fin.cast h a)) (fun a => μ (Fin.cast h a)) e ↔ ExpLe l r ν μ e := by
  subst h
  exact Iff.rfl
end Formalism.CohomologicalDescent.LD
