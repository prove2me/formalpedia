-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin19_original_positive_clock_measure_uniform_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T07:51:31.955372+00:00
-- url     : https://prove2.me/submissions/497e2097-9ebe-4795-abf1-af20ca33a14f

import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A : Set Ω) (σ : Ω → ℝ≥0) (L : ℕ → Ω → ℝ≥0)
    (hLle : ∀ k ω, L k ω ≤ σ ω)
    (a : ℝ) (ha : 0 ≤ a)
    (hPfinite : P (A ∩ {ω : Ω | σ ω ≠ 0}) ≠ ⊤)
    (R : ℕ → Ω → ℝ)
    (hLocal : ∀ k,
      (∫ ω in A ∩ {η : Ω | L k η ≠ 0}, R k ω ∂P) ≤
        a * (P (A ∩ {η : Ω | L k η ≠ 0})).toReal) :
    ∀ k, (∫ ω in A ∩ {η : Ω | L k η ≠ 0}, R k ω ∂P) ≤
      a * (P (A ∩ {η : Ω | σ η ≠ 0})).toReal := by
  intro k
  have hSub :
      A ∩ {η : Ω | L k η ≠ 0} ⊆
        A ∩ {η : Ω | σ η ≠ 0} := by
    intro ω hω
    obtain ⟨hA, hL⟩ := hω
    refine ⟨hA, ?_⟩
    intro hZero
    have hLzero : L k ω = 0 :=
      le_antisymm (by simpa [hZero] using hLle k ω) bot_le
    exact hL hLzero
  have hMass :
      P (A ∩ {η : Ω | L k η ≠ 0}) ≤
        P (A ∩ {η : Ω | σ η ≠ 0}) :=
    measure_mono hSub
  calc
    (∫ ω in A ∩ {η : Ω | L k η ≠ 0}, R k ω ∂P) ≤
        a * (P (A ∩ {η : Ω | L k η ≠ 0})).toReal :=
      hLocal k
    _ ≤ a * (P (A ∩ {η : Ω | σ η ≠ 0})).toReal :=
      mul_le_mul_of_nonneg_left
        (ENNReal.toReal_mono hPfinite hMass) ha
