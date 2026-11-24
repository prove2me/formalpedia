-- Prove2me | solution 1 for Formalism.CohomologicalDescent.UnitNormBounds.counts_deep_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:24:56.698132+00:00
-- url     : https://prove2.me/submissions/7d7b521c-c609-43b3-8185-141b10dc6bb9

import Definitions.Def_Formalism_PieriBlockIdeals_FactorialValuationSum
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LabelSumNeedsLeFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
import Theorems.Thm_Formalism_CohomologicalDescent_UnitNormBounds_rowStart_rev_eq
import Theorems.Thm_Formalism_CohomologicalDescent_UnitNormBounds_content_label_eq

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
theorem _root_.solution : CountsDeep := by
  intro k j t w M i lam xm xp hR tau htau ct hct
  have hb : ∀ a, w ≤ lam a ∧ lam a ≤ M := fun a => ⟨hR.low a, hR.high a⟩
  obtain ⟨hpi, _, hsum, _, _⟩ := Finset.mem_filter.mp htau
  have hle : ∀ b, dual M lam b ≤ tau b := fun b => (Finset.mem_Icc.mp ((Fintype.mem_piFinset.mp hpi) b)).1
  have htot : ∑ b : Fin (k + j), ((tau b : ℤ) - (dual M lam b : ℤ)) = (i : ℤ) := by
    rw [Finset.sum_sub_distrib]
    have : ((∑ a, tau a : ℕ) : ℤ) = ((∑ a, dual M lam a + i : ℕ) : ℤ) := by rw [hsum]
    push_cast at this
    linarith
  unfold cloudBoxes
  rw [← htot, ← nsmul_eq_mul, ← Finset.sum_const]
  refine le_trans (Finset.sum_le_sum ?_) (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_)
  · intro b hbm
    obtain ⟨_, h1, h2, h3⟩ := Finset.mem_filter.mp hbm
    have hU := rowStart_rev_eq k j t w M lam hb b
    have hc := content_label_eq t w M (le_trans (hb b).1 (hb b).2) ct
    have hr := (hR.cloud (Fin.rev b) h1).1
    omega
  · intro b _ _
    have := hle b
    omega
end Formalism.CohomologicalDescent.UnitNormBounds
