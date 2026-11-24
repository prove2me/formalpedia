-- Prove2me | solution 1 for Formalism.CohomologicalDescent.UnitNormBounds.boxesOfLabel_le_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:34:49.409468+00:00
-- url     : https://prove2.me/submissions/fd99a4bd-8ffb-4a9e-9aa2-e69c2010fd4f

import Definitions.Def_Formalism_PieriBlockIdeals_FactorialValuationSum
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LabelSumNeedsLeFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
import Theorems.Thm_Formalism_CohomologicalDescent_UnitNormBounds_counts_rows_holds
import Theorems.Thm_Formalism_CohomologicalDescent_UnitNormBounds_counts_cloud_holds
import Theorems.Thm_Formalism_CohomologicalDescent_UnitNormBounds_counts_deep_holds

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
theorem _root_.solution (k j t w M i : ℕ) (lam : Fin (k + j) → ℕ) (xm xp : ℤ) (hR : Rows k j t w M lam xm xp)
    (tau : Fin (k + j) → ℕ) (htau : tau ∈ shapes t (M - w) i (dual M lam)) (ct : ℤ) :
    (boxesOfLabel t w M lam tau ct : ℝ) ≤
      (if ct < xm then (j : ℝ) else 0) +
        min (min (k : ℝ) (t : ℝ)) (if ct < xm then (i : ℝ) / ((xm - ct : ℤ) : ℝ) else (k : ℝ)) := by
  have h1 := counts_rows_holds k j t w M i lam xm xp hR tau htau ct
  have h2 := counts_cloud_holds k j t w M i lam tau htau ct
  have hk : (cloudBoxes k j t w M lam tau ct : ℝ) ≤ k := by exact_mod_cast h2.1
  have ht : (cloudBoxes k j t w M lam tau ct : ℝ) ≤ t := by exact_mod_cast h2.2
  by_cases hct : ct < xm
  · rw [if_pos hct] at h1
    rw [if_pos hct, if_pos hct]
    have h1' : (boxesOfLabel t w M lam tau ct : ℝ) ≤ (j : ℝ) + (cloudBoxes k j t w M lam tau ct : ℝ) := by
      exact_mod_cast h1
    have h3 := counts_deep_holds k j t w M i lam xm xp hR tau htau ct hct
    have h3' : (cloudBoxes k j t w M lam tau ct : ℝ) * ((xm - ct : ℤ) : ℝ) ≤ (i : ℝ) := by exact_mod_cast h3
    have hpos : (0 : ℝ) < ((xm - ct : ℤ) : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) < xm - ct)
    have h4 : (cloudBoxes k j t w M lam tau ct : ℝ) ≤ (i : ℝ) / ((xm - ct : ℤ) : ℝ) := (le_div_iff₀ hpos).mpr h3'
    have h5 := le_min (le_min hk ht) h4
    linarith
  · rw [if_neg hct] at h1
    rw [if_neg hct, if_neg hct]
    have h1' : (boxesOfLabel t w M lam tau ct : ℝ) ≤ (0 : ℝ) + (cloudBoxes k j t w M lam tau ct : ℝ) := by
      exact_mod_cast h1
    have h5 := le_min (le_min hk ht) hk
    linarith
end Formalism.CohomologicalDescent.UnitNormBounds
