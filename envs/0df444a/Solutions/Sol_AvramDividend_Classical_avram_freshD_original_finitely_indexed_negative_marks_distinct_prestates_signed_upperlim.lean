-- Prove2me | solution 1 for AvramDividend.Classical.avram_freshD_original_finitely_indexed_negative_marks_distinct_prestates_signed_upperlim
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T09:02:07.380402+00:00
-- url     : https://prove2.me/submissions/6559b054-fe20-484f-bb19-8844542ecf9f

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.SetSemiring
import Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps14_original_capped_C2_fixed_negative_mark_upperlim
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {ι : Type*}
    (w : ℝ → ℝ) (cap : ℝ≥0∞) (c : ℝ) (hc : 0 < c)
    (hcCap : ENNReal.ofReal c ≤ cap)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < cap})
    (hw0 : 0 ≤ w 0) (hwcont : ContinuousOn w (Ici (0 : ℝ)))
    (hwneg : ∀ y : ℝ, y < 0 → w y = 0)
    (S : Finset ι) (z y : ι → ℝ)
    (hz : ∀ i ∈ S, z i < 0)
    (hy : ∀ i ∈ S, y i ∈ Ioo (0 : ℝ) c)
    (u : ℕ → ι → ℝ)
    (hu : ∀ i ∈ S, Tendsto (fun m => u m i) atTop (𝓝 (y i))) :
    Tendsto
      (fun m => max
        (∑ i ∈ S,
          ((w (u m i + z i) - w (u m i) -
            (if -1 < z i then z i * deriv w (u m i) else 0)) -
          (w (y i + z i) - w (y i) -
            (if -1 < z i then z i * deriv w (y i) else 0)))) 0)
      atTop (𝓝 (0 : ℝ)) := by
  classical
  let E : ℕ → ι → ℝ := fun m i =>
    (w (u m i + z i) - w (u m i) -
      (if -1 < z i then z i * deriv w (u m i) else 0)) -
    (w (y i + z i) - w (y i) -
      (if -1 < z i then z i * deriv w (y i) else 0))
  have hOne (i : ι) (hi : i ∈ S) (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ m in atTop, E m i ≤ ε := by
    have he :=
      avram_ubv_ito_jumps14_original_capped_C2_fixed_negative_mark_upperlim
        w cap c hc hcCap hw_smooth hw0 hwcont hwneg
        (y i) (z i) (hy i hi) (hz i hi) (fun m => u m i)
        (hu i hi) ε hε
    filter_upwards [he] with m hm
    dsimp [E]
    linarith
  change Tendsto (fun m => max (∑ i ∈ S, E m i) 0)
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
    have hev : ∀ᶠ m in atTop, ∀ i ∈ S, E m i ≤ δ := by
      apply (Filter.eventually_all_finset S).2
      intro i hi
      exact hOne i hi δ hδ
    filter_upwards [hev] with m hm
    have hs : (∑ i ∈ S, E m i) ≤ (S.card : ℝ) * δ := by
      calc
        _ ≤ ∑ _i ∈ S, δ := by
          apply Finset.sum_le_sum
          intro i hi
          exact hm i hi
        _ = (S.card : ℝ) * δ := by simp [mul_comm]
    have hb : (S.card : ℝ) * δ < a := by
      dsimp [δ]
      have hd : 0 < ((S.card : ℝ) + 1) := by positivity
      calc
        (S.card : ℝ) * (a / ((S.card : ℝ) + 1)) =
            ((S.card : ℝ) * a) / ((S.card : ℝ) + 1) := by ring
        _ < a := (div_lt_iff₀ hd).2 (by nlinarith)
    exact max_lt (lt_of_le_of_lt hs hb) ha
