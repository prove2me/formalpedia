-- Prove2me | solution 1 for Formalism.CohomologicalDescent.UnitNormBounds.harmonic_positive_log_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:02:28.805733+00:00
-- url     : https://prove2.me/submissions/9bd7569a-6bbb-4db9-9e70-5d8861dcb365

import Definitions.Def_Formalism_PieriBlockIdeals_FactorialValuationSum
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LabelSumNeedsLeFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.UnitNormBounds
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
namespace Formalism.CohomologicalDescent.UnitNormBounds
theorem _root_.solution : HarmPosLog := by
  intro l h i hi
  have hil : 0 ≤ i / (l : ℝ) := div_nonneg hi (Nat.cast_nonneg _)
  constructor
  · unfold harm
    split_ifs with hlh
    · exact mul_nonneg hil (add_nonneg zero_le_one Real.posLog_nonneg)
    · refine mul_le_mul_of_nonneg_left ?_ hil
      have : Real.log ((h : ℝ) / (l : ℝ)) ≤ Real.posLog ((h : ℝ) / (l : ℝ)) := le_max_right _ _
      linarith
  · intro h1 h2
    unfold harm
    rw [if_neg (by omega)]
    have hl0 : (0 : ℝ) < (l : ℝ) := by exact_mod_cast h1
    have hx : (1 : ℝ) ≤ (h : ℝ) / (l : ℝ) := by
      rw [le_div_iff₀ hl0, one_mul]
      exact_mod_cast h2
    rw [Real.posLog_eq_log (by rw [abs_of_nonneg (by linarith)]; exact hx)]
end Formalism.CohomologicalDescent.UnitNormBounds
