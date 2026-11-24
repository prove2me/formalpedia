-- Prove2me | solution 1 for Formalism.CohomologicalDescent.RealLocalDeltaNabla.exponent_sum_log_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:32:45.8828+00:00
-- url     : https://prove2.me/submissions/87543b07-42ab-422e-9b54-49ecce4d8789

import Definitions.Def_Formalism_PieriBlockIdeals_LocalFaithfullyFlat
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ExactExponentLatticeIncl
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla
import Theorems.Thm_Formalism_CohomologicalDescent_LA_lambda_u_strict_anti
import Theorems.Thm_Formalism_CohomologicalDescent_SL2BinomialLattices_nat_le_mul_log_real
import Theorems.Thm_Formalism_CohomologicalDescent_SL2BinomialLattices_raising_exponent_interval


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial TensorProduct
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.RealLocalDeltaNabla
open Formalism.GradedWeylDivisibility Formalism.UG Formalism.RankGapBounds.JumpSetsAlt Formalism.RankGapBounds.FormsTensorLocalization Formalism.CohomologicalDescent.LA Formalism.CohomologicalDescent.SL2BinomialLattices
namespace Formalism.CohomologicalDescent.RealLocalDeltaNabla
theorem _root_.solution : ESumLogBound := by
  intro ι _ r n ν hν l hl lo h hr
  have hI := fun i => raising_exponent_interval l (r i) (h i) (lamU (r i) (n i) (ν i)) (lo i) hl
    (lambda_u_strict_anti (r i) (n i) (ν i) (hν i)) (hr i)
  constructor
  · unfold eSum
    push_cast
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ => nat_le_mul_log_real _ _ _ _ (hI i).1
  · intro hh
    exact Finset.sum_eq_zero fun i _ => (hI i).2 (hh i)
end Formalism.CohomologicalDescent.RealLocalDeltaNabla
