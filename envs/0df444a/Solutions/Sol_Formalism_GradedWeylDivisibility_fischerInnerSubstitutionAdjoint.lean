-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.fischerInnerSubstitutionAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:11:53.218119+00:00
-- url     : https://prove2.me/submissions/2402f3f4-5aa7-47aa-acbf-55f3f7a25b8a

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockSubAdj
import Theorems.Thm_Formalism_GradedWeylDivisibility_LFocks_subAdj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.REAL
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution : FockSubAdj :=
  fun _ _ _ U f g => LFocks_subAdj U f g
end Formalism.GradedWeylDivisibility
