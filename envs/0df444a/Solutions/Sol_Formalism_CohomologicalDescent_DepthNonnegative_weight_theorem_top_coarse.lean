-- Prove2me | solution 1 for Formalism.CohomologicalDescent.DepthNonnegative.weight_theorem_top_coarse
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:19:28.099461+00:00
-- url     : https://prove2.me/submissions/aefa87b5-ab38-412d-af11-67ed0bfa441e

import Definitions.Def_Formalism_PieriBlockIdeals_BlockIdealBound5Derived
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointCorollaryFiveBound
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDbasisLemmas
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Theorems.Thm_Formalism_CohomologicalDescent_DepthNonnegative_weight_theorem_top
import Theorems.Thm_Formalism_CohomologicalDescent_DepthNonnegative_top_inclusion_monotone_holds
import Theorems.Thm_Formalism_CohomologicalDescent_UnitNormBounds_c_prime_le_coarse_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.DepthNonnegative
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds
namespace Formalism.CohomologicalDescent.DepthNonnegative
theorem _root_.solution : TheoremWTopCoarse := by
  intro hD O _ _ _ A _ _ G _ Γ K jK ι _ _ l N k t h lam T2 j q xm xp ecl ex i _ _ T _ _ _ _ S ϖ n₀ e Λ L
    _ _ _ _ _ hwt hT
  have hl : l.Prime := hT.1
  refine top_inclusion_monotone_holds O A G Γ K jK ι l N lam T S _ _ ?_
    (weight_theorem_top hD O A G Γ K jK ι l N k t h lam T2 j q xm xp ecl ex i T S ϖ n₀ e Λ L hwt hT).1
  apply Finset.sum_le_sum
  intro τ _
  unfold cTau
  split_ifs
  · exact min_le_min le_rfl (Nat.floor_le_floor
      (c_prime_le_coarse_holds l k (j τ) t (q τ) h N (ecl τ) _ _ _ _ hl.two_le (Nat.cast_nonneg _)))
  · exact le_rfl
end Formalism.CohomologicalDescent.DepthNonnegative
