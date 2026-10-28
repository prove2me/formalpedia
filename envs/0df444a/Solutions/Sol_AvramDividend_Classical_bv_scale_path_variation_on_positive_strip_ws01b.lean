-- Prove2me | solution 1 for AvramDividend.Classical.bv_scale_path_variation_on_positive_strip_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T14:30:16.638309+00:00
-- url     : https://prove2.me/submissions/b5804b08-6e7f-41f2-a763-c907485cc06f

import Mathlib
import Theorems.Thm_AvramDividend_Classical_bv_actual_path_partition_variation_bound_ws01b
import Theorems.Thm_AvramDividend_Classical_bv_scale_lipschitzOn_positive_compact_ws01b

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Positive-strip stopped scale payoffs inherit actual BV path variation.
No regularity is assumed at the origin. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (ε a x : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ≥0, ∀ᵐ ω ∂P, ∀ u : ℕ → ℝ≥0,
      Monotone u → ∀ n : ℕ,
      (∀ i : ℕ, i ≤ n → x + X.X (u i) ω ∈ Icc ε a) →
      (∑ i ∈ Finset.range n,
        |W (x + X.X (u (i + 1)) ω) - W (x + X.X (u i) ω)|) ≤
        (K : ℝ) * (2 * X.drift * ((u n : ℝ) - (u 0 : ℝ)) -
          (X.X (u n) ω - X.X (u 0) ω)) := by
  obtain ⟨K, hK⟩ :=
    bv_scale_lipschitzOn_positive_compact_ws01b
      X hX q hq W hW hBV ε a hε
  refine ⟨K, ?_⟩
  filter_upwards [bv_actual_path_partition_variation_bound_ws01b X hX hBV]
    with ω hVar
  intro u hu n hStrip
  have hstep : ∀ i ∈ Finset.range n,
      |W (x + X.X (u (i + 1)) ω) - W (x + X.X (u i) ω)| ≤
        (K : ℝ) * |X.X (u (i + 1)) ω - X.X (u i) ω| := by
    intro i hi
    have hi1 : i + 1 ≤ n := Nat.succ_le_of_lt (Finset.mem_range.mp hi)
    have hi0 : i ≤ n := le_trans (Nat.le_succ i) hi1
    have hbound :=
      hK.norm_sub_le (hStrip (i + 1) hi1) (hStrip i hi0)
    simpa [Real.norm_eq_abs, sub_eq_add_neg, add_assoc,
      add_left_comm, add_comm] using hbound
  have hsum := Finset.sum_le_sum hstep
  calc
    (∑ i ∈ Finset.range n,
      |W (x + X.X (u (i + 1)) ω) - W (x + X.X (u i) ω)|)
        ≤ ∑ i ∈ Finset.range n,
            (K : ℝ) * |X.X (u (i + 1)) ω - X.X (u i) ω| := hsum
    _ = (K : ℝ) * (∑ i ∈ Finset.range n,
            |X.X (u (i + 1)) ω - X.X (u i) ω|) := by
          rw [Finset.mul_sum]
    _ ≤ (K : ℝ) * (2 * X.drift * ((u n : ℝ) - (u 0 : ℝ)) -
          (X.X (u n) ω - X.X (u 0) ω)) :=
        mul_le_mul_of_nonneg_left (hVar u hu n) K.coe_nonneg
