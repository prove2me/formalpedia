-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.depth_two_of_dual_weights
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:21:25.625621+00:00
-- url     : https://prove2.me/submissions/b4f18f81-1979-46d8-b474-02589c2a760e

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_CohomologicalDescent_LD_depth_two_cast
import Theorems.Thm_Formalism_CohomologicalDescent_LD_depth2Dual


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
theorem _root_.solution (p q M : ℕ) (ξ : Fin (q + p) → ℤ) (lam μ : Fin (q + p) → ℕ)
    (hl : ∀ a, lam a ≤ M) (hm : ∀ a, μ a ≤ M) :
    depth2 (fun a : Fin (p + q) => -ξ (Fin.rev (Fin.cast (Nat.add_comm p q) a)))
      (fun a => dualWt M lam (Fin.cast (Nat.add_comm p q) a))
      (fun a => dualWt M μ (Fin.cast (Nat.add_comm p q) a)) = depth2 ξ lam μ :=
  (depth_two_cast (Nat.add_comm p q) (fun a => -ξ (Fin.rev a)) (dualWt M lam) (dualWt M μ)).trans
    (depth2Dual _ M ξ lam μ hl hm).1
end Formalism.CohomologicalDescent.LD
