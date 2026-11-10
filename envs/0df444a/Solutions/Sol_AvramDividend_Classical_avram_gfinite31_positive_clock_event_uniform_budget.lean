-- Prove2me | solution 1 for AvramDividend.Classical.avram_gfinite31_positive_clock_event_uniform_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T04:08:25.076933+00:00
-- url     : https://prove2.me/submissions/7654451f-c349-43c5-adc2-f58b0e45a73f

import Mathlib.MeasureTheory.Integral.Bochner.Set
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- A smaller positive stopped clock inherits a uniform initial-event budget. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (hA : MeasurableSet A)
    (σ : Ω → ℝ≥0) (L : ℕ → Ω → ℝ≥0)
    (hLmeas : ∀ j, Measurable (L j))
    (hLle : ∀ j ω, L j ω ≤ σ ω)
    (R : (Ω → ℝ≥0) → Ω → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (hLocal : ∀ j,
      (∫ ω in A ∩ {η : Ω | L j η ≠ 0}, R (L j) ω ∂P) ≤
      a * (P (A ∩ {η : Ω | L j η ≠ 0})).toReal) :
    ∀ j, (∫ ω in A ∩ {η : Ω | L j η ≠ 0},
      (if L j ω = 0 then a else R (L j) ω) ∂P) ≤
      a * (P (A ∩ {η : Ω | σ η ≠ 0})).toReal := by
  intro j
  have hN : MeasurableSet {ω : Ω | L j ω ≠ 0} := by
    have hz : MeasurableSet {ω : Ω | L j ω = 0} :=
      (hLmeas j) (measurableSet_singleton (0 : ℝ≥0))
    simpa only [Set.compl_setOf] using hz.compl
  have hE : MeasurableSet (A ∩ {η : Ω | L j η ≠ 0}) := hA.inter hN
  have hSub : A ∩ {η : Ω | L j η ≠ 0} ⊆
      A ∩ {η : Ω | σ η ≠ 0} := by
    intro ω hω
    refine ⟨hω.1, ?_⟩
    intro hz
    have hzero : L j ω = 0 :=
      le_antisymm (by simpa only [hz] using hLle j ω) zero_le
    exact hω.2 hzero
  have hMeasure : (P (A ∩ {η : Ω | L j η ≠ 0})).toReal ≤
      (P (A ∩ {η : Ω | σ η ≠ 0})).toReal :=
    ENNReal.toReal_mono (measure_ne_top P _) (measure_mono hSub)
  calc
    (∫ ω in A ∩ {η : Ω | L j η ≠ 0},
      (if L j ω = 0 then a else R (L j) ω) ∂P) =
      (∫ ω in A ∩ {η : Ω | L j η ≠ 0}, R (L j) ω ∂P) := by
        apply setIntegral_congr_fun hE
        intro ω hω
        simp only [if_neg hω.2]
    _ ≤ a * (P (A ∩ {η : Ω | L j η ≠ 0})).toReal := hLocal j
    _ ≤ a * (P (A ∩ {η : Ω | σ η ≠ 0})).toReal :=
      mul_le_mul_of_nonneg_left hMeasure ha
