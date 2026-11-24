-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.INST.sandwichDomain_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:48.170977+00:00
-- url     : https://prove2.me/submissions/7b97db8c-d30f-4dc0-b5d3-db2f5f906e65

import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SpreadSquare
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_Assemble
import Theorems.Thm_Formalism_GradedWeylDivisibility_weylLeDual


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.INST
open Formalism.GradedWeylDivisibility
namespace Formalism.InvariantFactorPaths.INST
theorem _root_.solution (h : SandwichZ) (hA : AscentDomain) : SandwichDomain := by
  intro p _ r n hn ν hν l hl O _ _ hO
  exact ⟨hA p r n hn ν _ (h p r n hn ν hν l hl) O hO, weylLeDual O r n hn ν hν⟩
end Formalism.InvariantFactorPaths.INST
