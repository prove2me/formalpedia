-- Prove2me | solution 1 for AvramDividend.Classical.bv_weighted_scale_path_variation_on_positive_strip_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:54:00.412296+00:00
-- url     : https://prove2.me/submissions/aac41128-4ff7-4f21-ac5b-c24815654fb0

import Mathlib
import Theorems.Thm_AvramDividend_Classical_bv_scale_path_variation_on_positive_strip_ws01b

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (ε a x : ℝ) (hε : 0 < ε) (hεa : ε ≤ a) :
    ∃ K : ℝ≥0, ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0),
      Monotone u → ∀ (n : ℕ),
      (∀ i : ℕ, i ≤ n → x + X.X (u i) ω ∈ Icc ε a) →
      ∀ (d : ℕ → ℝ), Antitone d →
      (∀ i, 0 ≤ d i) → (∀ i, d i ≤ 1) →
      (∑ i ∈ Finset.range n,
        |d (i + 1) * W (x + X.X (u (i + 1)) ω) -
           d i * W (x + X.X (u i) ω)|) ≤
        (K : ℝ) *
          (2 * X.drift * ((u n : ℝ) - (u 0 : ℝ)) -
            (X.X (u n) ω - X.X (u 0) ω)) +
          W a * (d 0 - d n) := by
  obtain ⟨K, hK⟩ := bv_scale_path_variation_on_positive_strip_ws01b X hX q hq W hW hBV ε a x hε
  refine ⟨K, ?_⟩
  filter_upwards [hK] with ω hω
  intro u hu n hn d hd hd0 hd1
  have base := hω u hu n hn
  obtain ⟨-, hW0, -, hWm, -⟩ := hW
  set w : ℕ → ℝ := fun i => W (x + X.X (u i) ω) with hw
  have hwb : ∀ i, i ≤ n → 0 ≤ w i ∧ w i ≤ W a := by
    intro i hi
    have h := hn i hi
    refine ⟨hW0 _ (by linarith [h.1]), hWm (by simp only [mem_Ici]; linarith [h.1])
      (by simp only [mem_Ici]; linarith) h.2⟩
  have term : ∀ i ∈ Finset.range n,
      |d (i + 1) * w (i + 1) - d i * w i| ≤ |w (i + 1) - w i| + W a * (d i - d (i + 1)) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    obtain ⟨h1, h2⟩ := hwb i hi'.le
    have hdi : d (i + 1) ≤ d i := hd (Nat.le_succ i)
    have e : d (i + 1) * w (i + 1) - d i * w i =
        d (i + 1) * (w (i + 1) - w i) - (d i - d (i + 1)) * w i := by ring
    rw [e]
    calc |d (i + 1) * (w (i + 1) - w i) - (d i - d (i + 1)) * w i|
        ≤ |d (i + 1) * (w (i + 1) - w i)| + |(d i - d (i + 1)) * w i| := abs_sub _ _
      _ ≤ |w (i + 1) - w i| + W a * (d i - d (i + 1)) := by
        refine add_le_add ?_ ?_
        · rw [abs_mul, abs_of_nonneg (hd0 _)]
          exact mul_le_of_le_one_left (abs_nonneg _) (hd1 _)
        · rw [abs_mul, abs_of_nonneg (by linarith), abs_of_nonneg h1, mul_comm]
          exact mul_le_mul_of_nonneg_right h2 (by linarith)
  calc _ ≤ ∑ i ∈ Finset.range n, (|w (i + 1) - w i| + W a * (d i - d (i + 1))) :=
        Finset.sum_le_sum term
    _ = (∑ i ∈ Finset.range n, |w (i + 1) - w i|) + W a * (d 0 - d n) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_range_sub']
    _ ≤ _ := by gcongr
