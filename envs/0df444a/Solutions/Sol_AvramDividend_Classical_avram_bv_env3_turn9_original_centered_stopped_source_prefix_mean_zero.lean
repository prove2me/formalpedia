-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_turn9_original_centered_stopped_source_prefix_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T22:15:45.070829+00:00
-- url     : https://prove2.me/submissions/607d8b4f-5a55-49f1-b123-044e1d8aa1df

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
noncomputable section

/-- A bounded measurable random stopped prefix has mean zero when
each measurably selected integrable original source increment is centred. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (m : ℕ) (k : Ω → ℕ)
    (hk : Measurable k) (hkBound : ∀ ω, k ω ≤ m)
    (f : ℕ → Ω → ℝ) (hf : ∀ i, Integrable (f i) P)
    (hMean : ∀ i < m,
      (∫ ω, (if i < k ω then f i ω else 0) ∂P) = 0) :
    (∫ ω, ∑ i ∈ Finset.range (k ω), f i ω ∂P) = 0 := by
  classical
  have hEq : (fun ω : Ω => ∑ i ∈ Finset.range (k ω), f i ω) =
      (fun ω : Ω => ∑ i ∈ Finset.range m,
        if i < k ω then f i ω else 0) := by
    funext ω
    have hfilter : (Finset.range m).filter
        (fun i => i < k ω) = Finset.range (k ω) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range]
      have hb := hkBound ω
      omega
    rw [Finset.sum_ite]
    simp only [Finset.sum_const_zero, add_zero]
    rw [hfilter]
  have hCell : ∀ i ∈ Finset.range m,
      Integrable (fun ω : Ω =>
        if i < k ω then f i ω else 0) P := by
    intro i hi
    have hs : MeasurableSet {ω : Ω | i < k ω} :=
      measurableSet_lt measurable_const hk
    have hfun : (fun ω : Ω => if i < k ω then f i ω else 0) =
        ({ω : Ω | i < k ω}.indicator (f i)) := by
      funext ω
      by_cases h : i < k ω <;> simp [Set.indicator_apply, h]
    rw [hfun]
    exact (hf i).indicator hs
  rw [hEq]
  rw [integral_finset_sum (Finset.range m) hCell]
  apply Finset.sum_eq_zero
  intro i hi
  exact hMean i (Finset.mem_range.mp hi)
