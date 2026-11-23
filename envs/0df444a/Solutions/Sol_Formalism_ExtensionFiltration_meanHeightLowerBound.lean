-- Prove2me | solution 1 for Formalism.ExtensionFiltration.meanHeightLowerBound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:39:47.291009+00:00
-- url     : https://prove2.me/submissions/e223360b-5a48-45a2-899e-e9a1c338d121

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_CombinedAverageDegreeBound
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_CombinedAverageDegreeBoundOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.ExtensionFiltration
namespace Formalism.ExtensionFiltration
theorem _root_.solution : MeanHeights := by
  intro ι _ _ h sl cs cc ρ X hρ0 hρ1 hX hpos hsl hmean
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  apply max_le
  · exact div_nonneg (Finset.sum_nonneg fun c _ => hpos c) hN.le
  · rw [le_div_iff₀ hN]
    rw [le_div_iff₀ hN] at hmean
    have hpt : ∀ c ∈ (univ : Finset ι), (1 - ρ) * (sl c + cs) - cc ≤ h c + cs := fun c _ => by
      have h1 := hsl c
      have h2 : sl c + cs ≤ max 0 (sl c + cs) := le_max_right _ _
      nlinarith
    have hsum := Finset.sum_le_sum hpt
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul] at hsum ⊢
    nlinarith [mul_nonneg (sub_nonneg.2 hρ1) (by linarith : (0 : ℝ) ≤ (∑ c, sl c) + X * Fintype.card ι),
      mul_nonneg (mul_nonneg hρ0 hX) hN.le]
end Formalism.ExtensionFiltration
