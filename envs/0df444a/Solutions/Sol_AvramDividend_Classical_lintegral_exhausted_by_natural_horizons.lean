-- Prove2me | solution 1 for AvramDividend.Classical.lintegral_exhausted_by_natural_horizons
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T09:45:51.734218+00:00
-- url     : https://prove2.me/submissions/7785286e-7bc0-450b-b359-5b6e50a725bf

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (μ : Measure ℝ) (f : ℝ → ℝ≥0∞) (hf : Measurable f)
    (S : Set ℝ) (hS : MeasurableSet S) :
    (∫⁻ t in S, f t ∂μ) =
      ⨆ n : ℕ, (∫⁻ t in S ∩ Iic (n : ℝ), f t ∂μ) := by
  classical
  let B : ℕ → Set ℝ := fun n => S ∩ Iic (n : ℝ)
  have hUnion : (⋃ n : ℕ, B n) = S := by
    ext t
    constructor
    · intro ht
      obtain ⟨n, hn⟩ := mem_iUnion.mp ht
      exact hn.1
    · intro ht
      obtain ⟨n, hn⟩ := exists_nat_ge t
      exact mem_iUnion.mpr ⟨n, ⟨ht, hn⟩⟩
  have hMeas (n : ℕ) : Measurable ((B n).indicator f) :=
    hf.indicator (hS.inter measurableSet_Iic)
  have hMono : Monotone (fun n : ℕ => (B n).indicator f) := by
    intro n m hnm
    apply Set.indicator_le_indicator_of_subset
    · intro t ht
      change t ∈ S ∧ t ≤ (n : ℝ) at ht
      change t ∈ S ∧ t ≤ (m : ℝ)
      exact ⟨ht.1, ht.2.trans (by exact_mod_cast hnm)⟩
    · intro t
      exact bot_le
  have hPoint (t : ℝ) :
      (⨆ n : ℕ, (B n).indicator f t) = S.indicator f t := by
    rw [← Set.indicator_iUnion_apply (by rfl) B f t, hUnion]
  calc
    (∫⁻ t in S, f t ∂μ) =
        ∫⁻ t, S.indicator f t ∂μ :=
      (lintegral_indicator hS f).symm
    _ = ∫⁻ t, ⨆ n : ℕ, (B n).indicator f t ∂μ := by
      congr 1
      funext t
      exact (hPoint t).symm
    _ = ⨆ n : ℕ, (∫⁻ t, (B n).indicator f t ∂μ) :=
      lintegral_iSup hMeas hMono
    _ = ⨆ n : ℕ, (∫⁻ t in B n, f t ∂μ) := by
      congr 1
      funext n
      exact lintegral_indicator (hS.inter measurableSet_Iic) f
    _ = ⨆ n : ℕ, (∫⁻ t in S ∩ Iic (n : ℝ), f t ∂μ) := rfl
