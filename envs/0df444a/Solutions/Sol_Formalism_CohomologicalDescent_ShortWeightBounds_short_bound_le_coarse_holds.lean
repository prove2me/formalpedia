-- Prove2me | solution 1 for Formalism.CohomologicalDescent.ShortWeightBounds.short_bound_le_coarse_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:31:31.627012+00:00
-- url     : https://prove2.me/submissions/4f1c03ae-bf23-473d-8b91-2240dbd317c4

import Definitions.Def_Formalism_PieriBlockIdeals_LatticeInclusionRealSettingAlt
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WeightBounds

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
theorem _root_.solution : Short6LeCoarse := by
  intro l k j t q h N' ecl xm xp mB I
  have e : cCoarse l k j t q h N' ecl xm xp mB I =
      cShort6 l k j t q h N' ecl xm xp mB I + 6 * ((q : ℝ) + 2 * (j : ℝ)) := by
    unfold cCoarse cShort6
    ring
  refine ⟨e, ?_⟩
  rw [e]
  have : (0 : ℝ) ≤ 6 * ((q : ℝ) + 2 * (j : ℝ)) := by positivity
  linarith
end Formalism.CohomologicalDescent.ShortWeightBounds
