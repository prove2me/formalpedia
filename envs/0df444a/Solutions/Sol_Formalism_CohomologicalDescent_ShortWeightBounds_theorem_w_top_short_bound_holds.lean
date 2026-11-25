-- Prove2me | solution 1 for Formalism.CohomologicalDescent.ShortWeightBounds.theorem_w_top_short_bound_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:08:27.007985+00:00
-- url     : https://prove2.me/submissions/325746c8-789c-4050-ada0-e04492f1c492

import Definitions.Def_Formalism_PieriBlockIdeals_LatticeInclusionRealSettingAlt
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WeightBounds
import Theorems.Thm_Formalism_CohomologicalDescent_ShortWeightBounds_c_prime_le_short_bound_holds
import Theorems.Thm_Formalism_CohomologicalDescent_DepthNonnegative_top_inclusion_monotone_holds
import Theorems.Thm_Formalism_CohomologicalDescent_DepthNonnegative_weight_theorem_top


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
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.ShortWeightBounds
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds
namespace Formalism.CohomologicalDescent.ShortWeightBounds
theorem _root_.solution : TheoremWTopShort6 := by
  intro hD O _ _ _ A _ _ G _ Γ K jK ι _ _ l N k t h lam T2 j q xm xp ecl ex i _ _ T _ _ _ _ S ϖ n₀ e Λ L
    _ _ _ _ _ hwt hT
  have hl : l.Prime := hT.1
  have key : TopIncl O Γ jK l N lam S
      (∑ τ, cTau T2 ex (cFloorShort6 l N k t h lam j q xm xp ecl i) τ) := by
    refine top_inclusion_monotone_holds O A G Γ K jK ι l N lam T S _ _ ?_
      (weight_theorem_top hD O A G Γ K jK ι l N k t h lam T2 j q xm xp ecl ex i T S ϖ n₀ e Λ L hwt hT).1
    apply Finset.sum_le_sum
    intro τ _
    unfold cTau
    split_ifs
    · exact min_le_min le_rfl (Nat.floor_le_floor
        (c_prime_le_short_bound_holds l k (j τ) t (q τ) h N (ecl τ) _ _ _ _ hl.two_le (Nat.cast_nonneg _)))
    · exact le_rfl
  exact ⟨key, Nat.sInf_le key⟩
end Formalism.CohomologicalDescent.ShortWeightBounds
