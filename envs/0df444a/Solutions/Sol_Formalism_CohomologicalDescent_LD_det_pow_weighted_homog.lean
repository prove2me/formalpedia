-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.det_pow_weighted_homog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:23:45.298623+00:00
-- url     : https://prove2.me/submissions/522f9028-24e4-4ffa-9829-20faf413ef45

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_CohomologicalDescent_LD_det_weighted_homog_ones
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_pow
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
theorem _root_.solution (r N : ℕ) : IsWeightedHomogeneous (rowW r r) (genericDet ℤ r ^ N) (fun _ => N) := by
  have h := (det_weighted_homog_ones r).pow N
  have e : (N • fun _ : Fin r => 1) = fun _ => N := by
    funext a
    simp
  rwa [e] at h
end Formalism.CohomologicalDescent.LD
