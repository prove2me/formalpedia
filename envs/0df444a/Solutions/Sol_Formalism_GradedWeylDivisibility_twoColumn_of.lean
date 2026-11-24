-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.twoColumn_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:08.672802+00:00
-- url     : https://prove2.me/submissions/d2428a6f-ea33-4565-9fa7-af8378c1f124

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_TwoColumn
import Theorems.Thm_Formalism_GradedWeylDivisibility_lctwo_main

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
theorem _root_.solution (h1 : PeelDecomp) (h2 : PeelHomog) (h3 : PeelLead) (h4 : PeelDegBound) : TwoColumn := by
  unfold TwoColumn
  intro B _ _ r n l j hlj a0 s ω g hg hω h0 hdeg
  exact lctwo_main h1 h2 h3 h4 B r n l j hlj (r - a0) a0 s ω g rfl hg hω h0 hdeg
end Formalism.GradedWeylDivisibility
