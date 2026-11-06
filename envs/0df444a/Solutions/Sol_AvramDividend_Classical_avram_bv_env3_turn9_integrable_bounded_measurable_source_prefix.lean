-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_turn9_integrable_bounded_measurable_source_prefix
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T22:11:51.754198+00:00
-- url     : https://prove2.me/submissions/b948ac68-6874-4ad9-8805-db6615672bf8

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- A measurable bounded random prefix of finitely many original source-grid
increments is integrable whenever each source-grid increment is integrable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (m : ℕ) (k : Ω → ℕ)
    (hk : Measurable k) (hkBound : ∀ ω, k ω ≤ m)
    (f : ℕ → Ω → ℝ) (hf : ∀ i, Integrable (f i) P) :
    Integrable (fun ω => ∑ i ∈ Finset.range (k ω), f i ω) P := by
  classical
  have hEq : (fun ω : Ω => ∑ i ∈ Finset.range (k ω), f i ω) =
      (fun ω : Ω => ∑ i ∈ Finset.range m,
        if i < k ω then f i ω else 0) := by
    funext ω
    have hfilter : (Finset.range m).filter
        (fun i => i < k ω) = Finset.range (k ω) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range]
      have hbound := hkBound ω
      omega
    rw [Finset.sum_ite]
    simp only [Finset.sum_const_zero, add_zero]
    rw [hfilter]
  have hInt : Integrable
      (fun ω : Ω => ∑ i ∈ Finset.range m,
        if i < k ω then f i ω else 0) P := by
    apply integrable_finset_sum
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
  exact hInt
