-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.depth_two_cast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:10:10.246258+00:00
-- url     : https://prove2.me/submissions/73a91f25-4c44-40cf-bd3b-2f15e174ed03

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
theorem _root_.solution {r r' : ℕ} (h : r' = r) (ξ : Fin r → ℤ) (lam μ : Fin r → ℕ) :
    depth2 (fun a => ξ (Fin.cast h a)) (fun a => lam (Fin.cast h a)) (fun a => μ (Fin.cast h a)) =
      depth2 ξ lam μ := by
  subst h
  rfl
end Formalism.CohomologicalDescent.LD
