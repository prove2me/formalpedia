-- Prove2me | solution 1 for AvramDividend.Classical.avram_freshD_original_fixed_finite_negative_marks_capped_Taylor_signed_positive_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T08:51:13.580569+00:00
-- url     : https://prove2.me/submissions/17fa81b5-f9af-4d9a-b37c-f36325b5abf0

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps14_original_capped_C2_fixed_negative_mark_upperlim
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (w : ℝ → ℝ) (cap : ℝ≥0∞) (c : ℝ) (hc : 0 < c)
    (hcCap : ENNReal.ofReal c ≤ cap)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < cap})
    (hw0 : 0 ≤ w 0) (hwcont : ContinuousOn w (Ici (0 : ℝ)))
    (hwneg : ∀ y : ℝ, y < 0 → w y = 0)
    (y : ℝ) (hy : y ∈ Ioo (0 : ℝ) c)
    (S : Finset ℝ) (hS : ∀ z ∈ S, z < 0)
    (u : ℕ → ℝ) (hu : Tendsto u atTop (𝓝 y)) :
    Tendsto
      (fun m => max
        (∑ z ∈ S,
          ((w (u m + z) - w (u m) -
            (if -1 < z then z * deriv w (u m) else 0)) -
          (w (y + z) - w y -
            (if -1 < z then z * deriv w y else 0)))) 0)
      atTop (𝓝 (0 : ℝ)) := by
  classical
  let E : ℕ → ℝ → ℝ := fun m z =>
    (w (u m + z) - w (u m) -
      (if -1 < z then z * deriv w (u m) else 0)) -
    (w (y + z) - w y -
      (if -1 < z then z * deriv w y else 0))
  have hOne (z : ℝ) (hz : z ∈ S) (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ m in atTop, E m z ≤ ε := by
    have he :=
      avram_ubv_ito_jumps14_original_capped_C2_fixed_negative_mark_upperlim
        w cap c hc hcCap hw_smooth hw0 hwcont hwneg
        y z hy (hS z hz) u hu ε hε
    filter_upwards [he] with m hm
    dsimp [E]
    linarith
  change Tendsto (fun m => max (∑ z ∈ S, E m z) 0)
    atTop (𝓝 (0 : ℝ))
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    filter_upwards [] with m
    exact lt_of_lt_of_le ha (le_max_right _ _)
  · intro a ha
    let δ : ℝ := a / ((S.card : ℝ) + 1)
    have hδ : 0 < δ := by
      dsimp [δ]
      positivity
    have hev : ∀ᶠ m in atTop, ∀ z ∈ S, E m z ≤ δ := by
      apply (Filter.eventually_all_finset S).2
      intro z hz
      exact hOne z hz δ hδ
    filter_upwards [hev] with m hm
    have hs : (∑ z ∈ S, E m z) ≤ (S.card : ℝ) * δ := by
      calc
        _ ≤ ∑ _z ∈ S, δ := by
          apply Finset.sum_le_sum
          intro z hz
          exact hm z hz
        _ = (S.card : ℝ) * δ := by simp [mul_comm]
    have hb : (S.card : ℝ) * δ < a := by
      dsimp [δ]
      have hd : 0 < ((S.card : ℝ) + 1) := by positivity
      calc
        (S.card : ℝ) * (a / ((S.card : ℝ) + 1)) =
            ((S.card : ℝ) * a) / ((S.card : ℝ) + 1) := by ring
        _ < a := (div_lt_iff₀ hd).2 (by nlinarith)
    exact max_lt (lt_of_le_of_lt hs hb) ha
