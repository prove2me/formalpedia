-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_marked_disjoint_cell_domination
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:50:13.014198+00:00
-- url     : https://prove2.me/submissions/c4dbf360-6852-4104-8549-61fda02f1a23

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_chat24_disjoint_cell_step_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem solution
    (μ : Measure (ℝ≥0 × ℝ)) (B : ℝ≥0)
    (u : ℕ → ℕ → ℝ≥0) (hu : ∀ n, StrictMono (u n))
    (hcap : ∀ n i, i ∈ Finset.range (n + 1) → u n (i + 1) ≤ B)
    (c : ℕ → ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C) (n0 : ℕ)
    (hc : ∀ n, n0 ≤ n → ∀ i ∈ Finset.range (n + 1), ‖c n i‖ ≤ C)
    (hsupport : ∀ᵐ p ∂μ, 0 < p.1 ∧ p.2 < 0) :
    let F : ℕ → ℝ≥0 × ℝ → ℝ := fun n p => if n0 ≤ n then
      ∑ i ∈ Finset.range (n + 1),
        if u n i < p.1 ∧ p.1 ≤ u n (i + 1) then c n i * (-p.2) else 0
      else 0
    let D : ℝ≥0 × ℝ → ℝ := fun p =>
      if 0 < p.1 ∧ p.1 ≤ B ∧ p.2 < 0 then C * (-p.2) else 0
    (∀ n, AEStronglyMeasurable (F n) μ) ∧
      (∀ n, ∀ᵐ p ∂μ, ‖F n p‖ ≤ D p) := by
  classical
  intro F D
  let g : ℕ → ℝ≥0 → ℝ := fun n t => if n0 ≤ n then
    ∑ i ∈ Finset.range (n + 1), if u n i < t ∧ t ≤ u n (i + 1) then c n i else 0
    else 0
  have hgb : ∀ n t, ‖g n t‖ ≤ C :=
    (AvramDividend.Classical.avram_chat24_disjoint_cell_step_bound
      (0 : Measure ℝ≥0) u hu c C hC n0 hc).2
  have hfg (n : ℕ) (p : ℝ≥0 × ℝ) : F n p = g n p.1 * (-p.2) := by
    by_cases hn : n0 ≤ n
    · simp only [F, g, if_pos hn]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      split_ifs <;> simp only [zero_mul]
    · simp only [F, g, if_neg hn, zero_mul]
  have hFm (n : ℕ) : AEStronglyMeasurable (F n) μ := by
    apply Measurable.aestronglyMeasurable
    by_cases hn : n0 ≤ n
    · have hsum : Measurable (fun p : ℝ≥0 × ℝ =>
          ∑ i ∈ Finset.range (n + 1),
            if u n i < p.1 ∧ p.1 ≤ u n (i + 1) then c n i * (-p.2) else 0) := by
        apply Finset.measurable_sum
        intro i hi
        have hmc : Measurable (fun p : ℝ≥0 × ℝ => c n i * (-p.2)) :=
          measurable_const.mul measurable_snd.neg
        have hs : MeasurableSet {p : ℝ≥0 × ℝ | u n i < p.1 ∧ p.1 ≤ u n (i + 1)} := by
          measurability
        exact Measurable.ite hs hmc measurable_const
      simpa only [F, if_pos hn] using hsum
    · simpa only [F, if_neg hn] using
        (measurable_const : Measurable (fun _ : ℝ≥0 × ℝ => (0 : ℝ)))
  refine ⟨hFm, ?_⟩
  intro n
  filter_upwards [hsupport] with p hp
  by_cases hpB : p.1 ≤ B
  · have hmark : 0 ≤ -p.2 := neg_nonneg.mpr hp.2.le
    have hmarknorm : ‖-p.2‖ = -p.2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg hmark]
    rw [hfg, norm_mul, hmarknorm]
    change ‖g n p.1‖ * (-p.2) ≤
      if 0 < p.1 ∧ p.1 ≤ B ∧ p.2 < 0 then C * (-p.2) else 0
    rw [if_pos (show 0 < p.1 ∧ p.1 ≤ B ∧ p.2 < 0 from ⟨hp.1, hpB, hp.2⟩)]
    exact mul_le_mul_of_nonneg_right (hgb n p.1) hmark
  · have hg0 : g n p.1 = 0 := by
      dsimp only [g]
      split_ifs with hn
      · apply Finset.sum_eq_zero
        intro i hi
        exact if_neg (fun hic => hpB (hic.2.trans (hcap n i hi)))
      · rfl
    simp [hfg, hg0, D, hpB]
