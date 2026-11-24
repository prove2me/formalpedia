-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.highest_weight_line_tall
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:19.162868+00:00
-- url     : https://prove2.me/submissions/ee6a0d59-883e-440e-86a4-a2b767dbb4e7

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_HWLineTall
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylPoint
import Theorems.Thm_Formalism_GradedWeylDivisibility_lhwline_diag_tall
import Theorems.Thm_Formalism_GradedWeylDivisibility_lhwline_rowGen_eq
import Theorems.Thm_Formalism_GradedWeylDivisibility_lhwline_vanish


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
theorem _root_.solution : HWLineTall := by
  intro K _ _ r n ν ⟨s, hs, hνs⟩ f hf hdiv
  obtain ⟨hhom, hcol⟩ := (dualWeylPoint K r n ν f).mp hf
  refine lhwline_vanish f (fun a b hab => lhwline_rowGen_eq a b f (hdiv a b hab)) hcol ?_
  intro D hD
  exact lhwline_diag_tall ν s hs hνs f hhom D hD
end Formalism.GradedWeylDivisibility
