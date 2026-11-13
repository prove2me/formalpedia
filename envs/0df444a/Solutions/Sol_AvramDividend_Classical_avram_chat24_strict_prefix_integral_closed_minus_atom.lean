-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_strict_prefix_integral_closed_minus_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T13:40:39.497112+00:00
-- url     : https://prove2.me/submissions/6ac9b112-a158-4da3-b5c8-d816360f51a1

import Mathlib.MeasureTheory.Integral.DominatedConvergence
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

lemma strict_clock_cutoff_limit_local
    (c t : ℝ≥0) (v : ℝ) (u : ℕ → ℝ≥0)
    (hu : ∀ n, u n < t) (hl : Tendsto u atTop (nhds t)) :
    Tendsto (fun n => if c ≤ u n then v else 0) atTop
      (nhds (if c < t then v else 0)) := by
  classical
  by_cases h : c < t
  · simp only [if_pos h]
    apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => v) atTop (nhds v)).congr'
    filter_upwards [hl.eventually (Ioi_mem_nhds h)] with n hn
    simp [h, hn.le]
  · have hn (n : ℕ) : ¬ c ≤ u n := fun hle => h (lt_of_le_of_lt hle (hu n))
    simpa [h, hn] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))

lemma strict_clock_integral_subtract_atom_local
    {α : Type*} [MeasurableSpace α] (m : Measure α)
    (clock : α → ℝ≥0) (hc : Measurable clock) (f : α → ℝ) (t : ℝ≥0)
    (hf : Integrable (fun a => if clock a ≤ t then f a else 0) m) :
    (∫ a, if clock a < t then f a else 0 ∂m) =
      (∫ a, if clock a ≤ t then f a else 0 ∂m) -
        ∫ a, if clock a = t then f a else 0 ∂m := by
  classical
  have he : Integrable (fun a => if clock a = t then f a else 0) m := by
    have heq : {a | clock a = t}.indicator (fun a => if clock a ≤ t then f a else 0) =
        (fun a => if clock a = t then f a else 0) := by
      funext a
      by_cases ha : clock a = t <;> simp [ha]
    have hi : Integrable ({a | clock a = t}.indicator
        (fun a => if clock a ≤ t then f a else 0)) m :=
      hf.indicator (measurableSet_eq_fun hc measurable_const)
    rw [heq] at hi
    exact hi
  have hp : (fun a => if clock a < t then f a else 0) =
      (fun a => (if clock a ≤ t then f a else 0) - if clock a = t then f a else 0) := by
    funext a
    rcases lt_trichotomy (clock a) t with h | h | h
    · simp [h, h.le, ne_of_lt h]
    · simp [h]
    · simp [not_le_of_gt h, not_lt_of_ge h.le, ne_of_gt h]
  rw [hp, integral_sub hf he]

lemma strict_clock_integral_dominated_limit_local
    {α : Type*} [MeasurableSpace α] (m : Measure α)
    (clock : α → ℝ≥0) (hc : Measurable clock) (f : α → ℝ) (t : ℝ≥0)
    (hf : Integrable (fun a => if clock a ≤ t then f a else 0) m)
    (u : ℕ → ℝ≥0) (hu : ∀ n, u n < t) (hl : Tendsto u atTop (nhds t)) :
    Tendsto (fun n => ∫ a, if clock a ≤ u n then f a else 0 ∂m) atTop
      (nhds (∫ a, if clock a < t then f a else 0 ∂m)) := by
  classical
  let g := fun a => if clock a ≤ t then f a else 0
  have hseq (n : ℕ) : (fun a => if clock a ≤ u n then g a else 0) =
      (fun a => if clock a ≤ u n then f a else 0) := by
    funext a
    by_cases h : clock a ≤ u n
    · simp [g, h, le_trans h (hu n).le]
    · simp [h]
  have hstrict : (fun a => if clock a < t then g a else 0) =
      (fun a => if clock a < t then f a else 0) := by
    funext a
    by_cases h : clock a < t
    · simp [g, h, h.le]
    · simp [h]
  have hlim : Tendsto (fun n => ∫ a, if clock a ≤ u n then g a else 0 ∂m) atTop
      (nhds (∫ a, if clock a < t then g a else 0 ∂m)) := by
    apply tendsto_integral_of_dominated_convergence (fun a => ‖g a‖)
    · intro n
      exact (hf.indicator (measurableSet_le hc measurable_const)).aestronglyMeasurable
    · exact hf.norm
    · intro n
      exact Filter.Eventually.of_forall (fun a => by
        by_cases h : clock a ≤ u n <;> simp [h, norm_nonneg])
    · exact Filter.Eventually.of_forall (fun a =>
        strict_clock_cutoff_limit_local (clock a) t (g a) u hu hl)
  simpa only [hseq, hstrict] using hlim

theorem solution
    {α : Type*} [MeasurableSpace α] (m : Measure α)
    (clock : α → ℝ≥0) (hc : Measurable clock)
    (f : α → ℝ) (t : ℝ≥0)
    (hf : Integrable (fun a => if clock a ≤ t then f a else 0) m)
    (u : ℕ → ℝ≥0) (hu : ∀ n, u n < t)
    (hl : Tendsto u atTop (nhds t)) :
    Tendsto (fun n => ∫ a, if clock a ≤ u n then f a else 0 ∂m) atTop
      (nhds ((∫ a, if clock a ≤ t then f a else 0 ∂m) -
        ∫ a, if clock a = t then f a else 0 ∂m)) := by
  have h := strict_clock_integral_dominated_limit_local m clock hc f t hf u hu hl
  rw [strict_clock_integral_subtract_atom_local m clock hc f t hf] at h
  exact h
