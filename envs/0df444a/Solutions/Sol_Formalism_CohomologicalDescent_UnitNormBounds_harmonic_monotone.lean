-- Prove2me | solution 1 for Formalism.CohomologicalDescent.UnitNormBounds.harmonic_monotone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:03:41.828769+00:00
-- url     : https://prove2.me/submissions/d0e868fd-2506-4743-979a-6df6ade76285

import Definitions.Def_Formalism_PieriBlockIdeals_FactorialValuationSum
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LabelSumNeedsLeFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.UnitNormBounds
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
namespace Formalism.CohomologicalDescent.UnitNormBounds
theorem _root_.solution (l h : ℕ) : Monotone (harm l h) := by
  intro a b hab
  unfold harm
  split_ifs with hlh
  · exact le_rfl
  · have hlog : 0 ≤ Real.log ((h : ℝ) / (l : ℝ)) := by
      rcases Nat.eq_zero_or_pos l with h0 | h0
      · rw [h0]; simp
      · have hl0 : (0 : ℝ) < (l : ℝ) := by exact_mod_cast h0
        refine Real.log_nonneg ?_
        rw [le_div_iff₀ hl0, one_mul]
        exact_mod_cast (by omega : l ≤ h)
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hab (Nat.cast_nonneg _)) (by linarith)
end Formalism.CohomologicalDescent.UnitNormBounds
