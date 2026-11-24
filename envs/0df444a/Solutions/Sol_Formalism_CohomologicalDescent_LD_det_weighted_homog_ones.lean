-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.det_weighted_homog_ones
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:13:15.810318+00:00
-- url     : https://prove2.me/submissions/830d88cc-a5ba-44f3-958b-981a56926a4d

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_CohomologicalDescent_LA_leading_minor_full_eq_det
import Theorems.Thm_Formalism_GradedWeylDivisibility_lpMinor_rowHom
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LA
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution (r : ℕ) : IsWeightedHomogeneous (rowW r r) (genericDet ℤ r) (fun _ => 1) := by
  have h := lpMinor_rowHom ℤ (r := r) (n := r) r le_rfl le_rfl
  rw [leading_minor_full_eq_det ℤ r rfl] at h
  have e : (fun a : Fin r => if a.val < r then 1 else 0) = fun _ => 1 := by
    funext a
    simp [a.isLt]
  rwa [e] at h
end Formalism.CohomologicalDescent.LD
