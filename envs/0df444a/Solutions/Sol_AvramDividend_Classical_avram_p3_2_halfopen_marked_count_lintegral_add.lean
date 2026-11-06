-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_halfopen_marked_count_lintegral_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T10:27:19.863475+00:00
-- url     : https://prove2.me/submissions/5147cdf7-ba2b-4973-93b3-068d74bcdde4

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_marked_count_nonlinear_lintegral_eq_tsum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Finite physical jump-cell partition: nonnegative marked-count integrals
split exactly over adjacent half-open clock intervals, preserving endpoint atoms. -/
theorem solution
    (S : Set ℝ≥0) (hS : MeasurableSet S)
    (mark : ℝ≥0 → ℝ≥0 × ℝ) (hmark : Measurable mark)
    (F : ℝ≥0 × ℝ → ℝ≥0∞) (hF : Measurable F)
    (a b c : ℝ≥0) (hab : a ≤ b) (hbc : b ≤ c) :
    (∫⁻ p, F p ∂((Measure.count.restrict (S ∩ Set.Ioc a c)).map mark)) =
      (∫⁻ p, F p ∂((Measure.count.restrict (S ∩ Set.Ioc a b)).map mark)) +
      (∫⁻ p, F p ∂((Measure.count.restrict (S ∩ Set.Ioc b c)).map mark)) := by
  classical
  have hCount (r t : ℝ≥0) :
      (∫⁻ p, F p ∂((Measure.count.restrict (S ∩ Set.Ioc r t)).map mark)) =
        ∑' x : ℝ≥0, if x ∈ S ∩ Set.Ioc r t then F (mark x) else 0 := by
    simpa only [Set.mem_inter_iff] using
      (avram_p3_2_original_marked_count_nonlinear_lintegral_eq_tsum
        (S ∩ Set.Ioc r t) (hS.inter measurableSet_Ioc) mark hmark F hF)
  calc
    (∫⁻ p, F p ∂((Measure.count.restrict (S ∩ Set.Ioc a c)).map mark))
        = ∑' x : ℝ≥0, if x ∈ S ∩ Set.Ioc a c then F (mark x) else 0 :=
          hCount a c
    _ = (∑' x : ℝ≥0, if x ∈ S ∩ Set.Ioc a b then F (mark x) else 0) +
        (∑' x : ℝ≥0, if x ∈ S ∩ Set.Ioc b c then F (mark x) else 0) := by
      rw [← ENNReal.tsum_add]
      apply tsum_congr
      intro x
      by_cases hs : x ∈ S
      · by_cases hl : x ∈ Set.Ioc a b
        · have hr : x ∉ Set.Ioc b c := by
            intro h
            exact (not_lt_of_ge hl.2) h.1
          have hac : x ∈ Set.Ioc a c := ⟨hl.1, le_trans hl.2 hbc⟩
          simp [Set.mem_inter_iff, hs, hl, hr, hac]
        · by_cases hr : x ∈ Set.Ioc b c
          · have hac : x ∈ Set.Ioc a c :=
              ⟨lt_of_le_of_lt hab hr.1, hr.2⟩
            simp [Set.mem_inter_iff, hs, hl, hr, hac]
          · have hnac : x ∉ Set.Ioc a c := by
              intro hx
              by_cases hxb : x ≤ b
              · exact hl ⟨hx.1, hxb⟩
              · exact hr ⟨lt_of_not_ge hxb, hx.2⟩
            simp [Set.mem_inter_iff, hs, hl, hr, hnac]
      · simp [Set.mem_inter_iff, hs]
    _ = (∫⁻ p, F p ∂((Measure.count.restrict (S ∩ Set.Ioc a b)).map mark)) +
        (∫⁻ p, F p ∂((Measure.count.restrict (S ∩ Set.Ioc b c)).map mark)) := by
      rw [hCount a b, hCount b c]
