-- Prove2me | solution 1 for Formalism.CohomologicalDescent.UnitNormBounds.c_prime_le_coarse_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:13:18.742648+00:00
-- url     : https://prove2.me/submissions/8fd53bbc-a6ad-48ab-b4ae-5c4a51c51707

import Definitions.Def_Formalism_PieriBlockIdeals_FactorialValuationSum
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LabelSumNeedsLeFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
import Theorems.Thm_Formalism_CohomologicalDescent_UnitNormBounds_harmonic_positive_log_holds

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
theorem _root_.solution : CPrimeLeCoarse := by
  intro l k j t q h N' ecl xm xp mB I hl hI
  unfold cPrime cCoarse labelSumBoundPos
  have h1 := (harmonic_positive_log_holds l h I hI).1
  have hl1 : (0 : ℝ) ≤ (l : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
    linarith
  have h2 : ((h : ℝ) - 1) / ((l : ℝ) - 1) ≤ ((h : ℝ) + (N' : ℝ)) / ((l : ℝ) - 1) + 6 := by
    have h3 : ((h : ℝ) - 1) / ((l : ℝ) - 1) ≤ ((h : ℝ) + (N' : ℝ)) / ((l : ℝ) - 1) :=
      div_le_div_of_nonneg_right (by have : (0 : ℝ) ≤ (N' : ℝ) := Nat.cast_nonneg _; linarith) hl1
    linarith
  have h4 := mul_le_mul_of_nonneg_left h2
    (by positivity : (0 : ℝ) ≤ (q : ℝ) + 2 * (j : ℝ))
  linarith
end Formalism.CohomologicalDescent.UnitNormBounds
