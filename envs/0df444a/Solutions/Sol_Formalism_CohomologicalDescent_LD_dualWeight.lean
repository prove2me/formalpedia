-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.dualWeight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:36:08.214862+00:00
-- url     : https://prove2.me/submissions/8e5d754b-01fc-419d-9a16-15ead11aff50

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_CohomologicalDescent_LD_gen_det_eq_det
import Theorems.Thm_Formalism_CohomologicalDescent_LD_genericDet_pow_ne_zero
import Theorems.Thm_Formalism_CohomologicalDescent_LD_cofactor_weighted_homog
import Theorems.Thm_Formalism_CohomologicalDescent_LD_det_pow_weighted_homog
import Theorems.Thm_Formalism_CohomologicalDescent_LA_weighted_homogeneous_cancel
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_mul
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
theorem _root_.solution : DualWeight := by
  intro r M μ x g hM hx hrel
  rw [gen_det_eq_det] at hrel
  refine weighted_homogeneous_cancel (rowW r r) (genericDet ℤ r ^ (∑ a, μ a)) g (fun _ => ∑ a, μ a) (dualWt M μ)
    (genericDet_pow_ne_zero r _) (det_pow_weighted_homog r _) ?_
  rw [hrel]
  have h := (det_pow_weighted_homog r M).mul (cofactor_weighted_homog μ x hx)
  have e : ((fun _ => M) + fun c => ∑ a, μ a - μ (Fin.rev c)) = (fun _ : Fin r => ∑ a, μ a) + dualWt M μ := by
    funext c
    have h1 := hM (Fin.rev c)
    have h2 : μ (Fin.rev c) ≤ ∑ a, μ a := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
    simp only [Pi.add_apply, dualWt]
    omega
  rwa [e] at h
end Formalism.CohomologicalDescent.LD
