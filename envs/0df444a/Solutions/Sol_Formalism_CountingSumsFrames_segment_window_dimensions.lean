-- Prove2me | solution 1 for Formalism.CountingSumsFrames.segment_window_dimensions
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:39.150846+00:00
-- url     : https://prove2.me/submissions/c86b252c-833c-48f7-b9c4-0d316b67094c

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentTopRoomPublished
import Theorems.Thm_Formalism_CountingSumsFrames_segment_window_ratio

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution : SegWindowDims := by
  intro p N N₁ r s A0 Y a b' Q La P A Clo Chi h hs hNY hP hlo hhi
  have hY : 1 ≤ Y := h.1
  have hY0 : 0 < Y := by linarith
  have hi : ∀ i, (dimPol r (Chi i) : ℝ) ≤ Real.exp (2 / Y) * dimPol r (Clo i) := fun i =>
    (segment_window_ratio p N N₁ r Y a b' Q La (P i) (Clo i) (Chi i) h (hP i).1 (hP i).2 (hlo i).1
      (hhi i).1 (hlo i).2 (hhi i).2).2
  have main : (dimMM r A0 A Chi : ℝ) ≤ Real.exp (2 * s / Y) * dimMM r A0 A Clo := by
    unfold dimMM
    push_cast
    have hprod : ∏ i, ((dimPol r (A i) : ℝ) * dimPol r (Chi i)) ≤
        ∏ i, (Real.exp (2 / Y) * ((dimPol r (A i) : ℝ) * dimPol r (Clo i))) := by
      apply Finset.prod_le_prod
      · intro i _; positivity
      · intro i _
        calc (dimPol r (A i) : ℝ) * dimPol r (Chi i)
            ≤ (dimPol r (A i) : ℝ) * (Real.exp (2 / Y) * dimPol r (Clo i)) := by
              gcongr; exact hi i
          _ = Real.exp (2 / Y) * ((dimPol r (A i) : ℝ) * dimPol r (Clo i)) := by ring
    have e : ∏ i, (Real.exp (2 / Y) * ((dimPol r (A i) : ℝ) * dimPol r (Clo i))) =
        Real.exp (2 * s / Y) * ∏ i, ((dimPol r (A i) : ℝ) * dimPol r (Clo i)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        ← Real.exp_nat_mul]
      congr 2
      ring
    rw [e] at hprod
    calc (dimPol r A0 : ℝ) * ∏ i, ((dimPol r (A i) : ℝ) * dimPol r (Chi i))
        ≤ (dimPol r A0 : ℝ) *
            (Real.exp (2 * s / Y) * ∏ i, ((dimPol r (A i) : ℝ) * dimPol r (Clo i))) := by gcongr
      _ = Real.exp (2 * s / Y) *
            ((dimPol r A0 : ℝ) * ∏ i, ((dimPol r (A i) : ℝ) * dimPol r (Clo i))) := by ring
  refine ⟨main, main.trans ?_⟩
  have hsY : (s : ℝ) ≤ Y := le_trans (by exact_mod_cast hs) hNY
  have harg : 2 * (s : ℝ) / Y ≤ 2 := by rw [div_le_iff₀ hY0]; linarith
  gcongr
end Formalism.CountingSumsFrames
