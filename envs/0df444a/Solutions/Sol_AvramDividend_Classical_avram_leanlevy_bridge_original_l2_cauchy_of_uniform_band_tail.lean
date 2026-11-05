-- Prove2me | solution 1 for AvramDividend.Classical.avram_leanlevy_bridge_original_l2_cauchy_of_uniform_band_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:02:50.416198+00:00
-- url     : https://prove2.me/submissions/cbbc67fb-fcea-426f-b25d-333fd64e1b46

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (M : ℕ → ℝ≥0 → Lp ℝ (2 : ℝ≥0∞) P)
    (ρ : ℕ → ℝ)
    (hTail : ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, ρ n < ε)
    (hBound : ∀ t n m, n ≤ m →
      dist (M n t) (M m t) ≤ ρ n) :
    ∀ t, CauchySeq (fun n => M n t) := by
  intro t
  refine Metric.cauchySeq_iff.mpr ?_
  intro ε hε
  obtain ⟨N, hN⟩ := hTail ε hε
  refine ⟨N, ?_⟩
  intro m hm n hn
  rcases le_total m n with hmn | hnm
  · exact lt_of_le_of_lt (hBound t m n hmn) (hN m hm)
  · rw [dist_comm]
    exact lt_of_le_of_lt (hBound t n m hnm) (hN n hn)
