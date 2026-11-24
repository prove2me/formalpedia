-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.componentDegree
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:27:59.527864+00:00
-- url     : https://prove2.me/submissions/bad1e967-7478-48da-8ad3-a8dc7f61e053

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LCcompLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_CompDeg
import Theorems.Thm_Formalism_GradedWeylDivisibility_lccomp_component_colAddGen
import Theorems.Thm_Formalism_GradedWeylDivisibility_lccomp_degreeOf_component_le


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
theorem _root_.solution : CompDeg := by
  intro B _ r n l j ω s f hf
  rw [← lccomp_component_colAddGen]
  exact (lccomp_degreeOf_component_le _ _ _ _).trans hf
end Formalism.GradedWeylDivisibility
