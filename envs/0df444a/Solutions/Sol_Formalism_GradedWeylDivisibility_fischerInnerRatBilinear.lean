-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.fischerInnerRatBilinear
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:42:06.979663+00:00
-- url     : https://prove2.me/submissions/a82212de-a4e3-44ee-9ff6-5f2281348be9

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockqLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQBilin
import Theorems.Thm_Formalism_GradedWeylDivisibility_lfockq_add_left
import Theorems.Thm_Formalism_GradedWeylDivisibility_lfockq_smul_left


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution : FockQBilin := fun _ f f' g c =>
  ⟨lfockq_add_left f f' g, lfockq_smul_left c f g⟩
end Formalism.GradedWeylDivisibility
