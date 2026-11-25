-- Prove2me | solution 1 for Formalism.CohomologicalDescent.DepthNonnegative.log_plus_versus_max_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:28:50.81201+00:00
-- url     : https://prove2.me/submissions/055a333a-91e3-4c84-8c4e-d916cb809d38

import Definitions.Def_Formalism_PieriBlockIdeals_BlockIdealBound5Derived
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointCorollaryFiveBound
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDbasisLemmas
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative

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
open Formalism.RankGapBounds.ChebyshevFactorialBounds
namespace Formalism.CohomologicalDescent.DepthNonnegative
theorem _root_.solution : LogPlusVsMax := by
  intro l h i hh hl hi
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hl0 : (0 : ℝ) < l := by
    have : (h : ℝ) < l := by exact_mod_cast hl
    linarith
  have hq0 : (0 : ℝ) < (h : ℝ) / (l : ℝ) := div_pos hh0 hl0
  have hq1 : (h : ℝ) / (l : ℝ) < 1 := by
    rw [div_lt_one hl0]
    exact_mod_cast hl
  have hlog : Real.log ((h : ℝ) / (l : ℝ)) < 0 := Real.log_neg hq0 hq1
  have hpos : Real.posLog ((h : ℝ) / (l : ℝ)) = 0 := by
    rw [Real.posLog_def]
    exact max_eq_left hlog.le
  rw [hpos, add_zero]
  apply mul_lt_mul_of_pos_left _ (div_pos hi hl0)
  rw [max_lt_iff]
  constructor <;> linarith
end Formalism.CohomologicalDescent.DepthNonnegative
