-- Prove2me | solution 1 for Formalism.CohomologicalDescent.UnitNormBounds.second_valuation_up_to_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:57:56.434637+00:00
-- url     : https://prove2.me/submissions/d9bf50e0-3934-4b4e-bcd3-1a4be9527129

import Definitions.Def_Formalism_PieriBlockIdeals_FactorialValuationSum
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LabelSumNeedsLeFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
import Theorems.Thm_Formalism_CohomologicalDescent_UnitNormBounds_labelRHSPlus_monotone
import Theorems.Thm_Formalism_CohomologicalDescent_UnitNormBounds_second_valuation_holds

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
theorem _root_.solution : Step2ValUpTo := by
  intro l k j t w M h i I lam xm xp hl hR hxp hh hiI
  have h1 := second_valuation_holds l k j t w M h i lam xm xp hl hR hxp hh
  have h2 := labelRHSPlus_monotone l k t h xm xp (maxB t w) hiI
  have hl1 : (0 : ℝ) ≤ (l : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl.two_le
    linarith
  have hD : ((xm - maxB t w : ℤ) : ℝ) ≤ (h : ℝ) := by
    have := hR.le
    exact_mod_cast (by omega : xm - maxB t w ≤ (h : ℤ))
  have h3 : (((xm - maxB t w : ℤ) : ℝ) - 1) / ((l : ℝ) - 1) ≤ ((h : ℝ) - 1) / ((l : ℝ) - 1) :=
    div_le_div_of_nonneg_right (by linarith) hl1
  have h4 := mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ))
  linarith
end Formalism.CohomologicalDescent.UnitNormBounds
