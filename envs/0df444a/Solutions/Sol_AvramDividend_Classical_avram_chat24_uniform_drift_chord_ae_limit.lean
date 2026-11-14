-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_uniform_drift_chord_ae_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:24:59.863236+00:00
-- url     : https://prove2.me/submissions/5c973b6b-957f-4e3a-99a4-b411fc75db43

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_chat24_uniform_drift_chord_pointwise_no_jump
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem solution
    (f P Y : ℝ≥0 → ℝ) (d a b q : ℝ) (ha : 0 < a)
    (B : ℝ≥0) (hB : 0 < B)
    (hf_right : ∀ t, ContinuousWithinAt f (Ici t) t)
    (hf_left : ∀ t : ℝ≥0, 0 < t → ∃ l, Tendsto f (𝓝[<] t) (nhds l))
    (hsum : Summable (fun t : ℝ≥0 =>
      if 0 < t ∧ t ≤ B then Function.leftLim f t - f t else 0))
    (hpre : ∀ t : ℝ≥0, 0 < t → t ≤ B →
      Y t ∈ Icc a b ∧ Tendsto P (𝓝[<] t) (nhds (Y t)))
    (w : ℝ → ℝ) (hw : ContDiffOn ℝ 1 w (Ioi 0))
    (n0 : ℕ) (μ : Measure ℝ≥0) (hμ : ∀ t : ℝ≥0, μ {t} = 0) :
    let u : ℕ → ℕ → ℝ≥0 := fun n i => B * (i : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)
    let h : ℕ → ℝ := fun n => (B : ℝ) / ((n + 1 : ℕ) : ℝ)
    let m : ℕ → ℕ → ℝ := fun n i =>
      d * h n - (f (u n (i + 1)) - f (u n i))
    let G : ℕ → ℝ≥0 → ℝ := fun n t => if n0 ≤ n then
      ∑ i ∈ Finset.range (n + 1),
        if u n i < t ∧ t ≤ u n (i + 1) then
          Real.exp (-(q * (u n (i + 1) : ℝ))) *
            ((w (P (u n i) + d * h n - m n i) - w (P (u n i) - m n i)) / h n)
        else 0
      else 0
    let A : ℝ≥0 → ℝ := fun t =>
      if (t : ℝ≥0∞) ≤ (B : ℝ≥0∞) ∧ Y t ∈ Icc a b then
        Real.exp (-(q * (t : ℝ))) * (d * deriv w (Y t)) else 0
    ∀ᵐ t ∂μ, Tendsto (fun n => G n t) atTop (nhds (A t)) := by
  letI : NullSingletonClass μ := ⟨hμ⟩
  have hz : ∀ᵐ t ∂μ,
      (if 0 < t ∧ t ≤ B then Function.leftLim f t - f t else 0) = 0 := by
    apply ae_iff.mpr
    exact Set.Countable.measure_zero (Summable.countable_support hsum) μ
  have hn : ∀ᵐ t ∂μ, t ≠ 0 := by
    apply ae_iff.mpr
    simpa using hμ 0
  dsimp only
  filter_upwards [hz, hn] with t ht hne
  have hpos : 0 < t := bot_lt_iff_ne_bot.mpr hne
  exact AvramDividend.Classical.avram_chat24_uniform_drift_chord_pointwise_no_jump
    f P Y d a b q ha B hB hf_right hf_left hpre w hw n0 t hpos ht
