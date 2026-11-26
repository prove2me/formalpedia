-- Prove2me | solution 1 for ClassicalComplexWPT.lastTaylorCoefficient_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:57:31.909483+00:00
-- url     : https://prove2.me/submissions/f4deb284-8b18-482f-8719-96e42b31582a

import Definitions.Def_ClassicalComplexWPT_ExactOrder
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Analytic.Uniqueness
import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Theorems.Thm_ClassicalComplexWPT_lastAxis_apply
import Theorems.Thm_ClassicalComplexWPT_lastSlice_zero
attribute [local simp] ClassicalComplexWPT.lastSlice_zero


attribute [local simp] ClassicalComplexWPT.lastAxis_apply

set_option autoImplicit true
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution {n k : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) :
    lastTaylorCoefficient p k 0 = p k (fun _ ↦ lastDirection n) := by
  classical
  unfold lastTaylorCoefficient FormalMultilinearSeries.changeOrigin
  rw [FormalMultilinearSeries.sum, tsum_eq_single 0]
  · simp only [FormalMultilinearSeries.changeOriginSeries]
    rw [Finset.sum_eq_single ⟨∅, by simp⟩]
    · exact FormalMultilinearSeries.changeOriginSeriesTerm_apply p k 0 ∅ (by simp)
        (0 : Ambient n) (lastDirection n)
    · intro b _ hb
      exact (hb (Subtype.ext (Finset.card_eq_zero.mp b.property))).elim
    · simp
  · intro b hb
    cases b with
    | zero => exact (hb rfl).elim
    | succ b =>
      apply ContinuousMultilinearMap.map_coord_zero _ (0 : Fin (b + 1))
      rfl
end ClassicalComplexWPT
