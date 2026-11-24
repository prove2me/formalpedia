-- Prove2me | solution 1 for Formalism.CohomologicalDescent.UnitNormBounds.multiplicity_bound_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:42:13.478073+00:00
-- url     : https://prove2.me/submissions/8e9813b2-bb65-429f-b452-6cd062f4ddf6

import Definitions.Def_Formalism_PieriBlockIdeals_FactorialValuationSum
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LabelSumNeedsLeFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
import Theorems.Thm_Formalism_CohomologicalDescent_UnitNormBounds_boxesOfLabel_le_bound
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
theorem _root_.solution : MuBound := by
  intro k j t w M i lam xm xp hR ct
  unfold mu
  by_cases hne : (shapes t (M - w) i (dual M lam)).Nonempty
  · obtain ⟨tau, htau, heq⟩ := Finset.exists_mem_eq_sup _ hne
      (fun tau => boxesOfContent (dual M lam) tau (cont t w M ct))
    rw [heq]
    exact boxesOfLabel_le_bound k j t w M i lam xm xp hR tau htau ct
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sup_empty]
    have h0 : (((⊥ : ℕ) : ℕ) : ℝ) = 0 := by simp
    rw [h0]
    refine add_nonneg (by split_ifs <;> positivity) (le_min (le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _)) ?_)
    split_ifs with hct
    · exact div_nonneg (Nat.cast_nonneg _) (by exact_mod_cast (by omega : (0 : ℤ) ≤ xm - ct))
    · exact Nat.cast_nonneg _
end Formalism.CohomologicalDescent.UnitNormBounds
