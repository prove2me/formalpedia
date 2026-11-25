-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.levelRecursion_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:54:44.176529+00:00
-- url     : https://prove2.me/submissions/16d41fec-a8d8-4aa8-a825-bac4cfc6de65

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelGrowthBounds
import Theorems.Thm_Formalism_FourierDecayAlt_P_LevelGrowthBounds_one_le_sqrt_e
import Theorems.Thm_Formalism_FourierDecayAlt_P_level_recursion_lower_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Real Formalism.FourierDecayAlt.P.LevelGrowthBounds
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.F7.LevelRecursion := by
  intro r ε δ e a hε hδ hδ2 he ha hrec
  refine level_recursion_lower_sum r ε δ e a hε hδ hδ2 he ha ?_
  intro i h1 h2
  have hS : 0 ≤ ∑ s ∈ Icc 2 i, δ ^ (s - 1) * a (i - s) :=
    Finset.sum_nonneg fun s _ => mul_nonneg (pow_nonneg hδ _) (ha _)
  have hq := one_le_sqrt_e he i
  have := hrec i h1 h2
  nlinarith [mul_le_mul_of_nonneg_right hq hS]
end Formalism.FourierDecayAlt.P
