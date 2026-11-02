-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_02a_first_candidate_filter_covers_original_jumps
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:43:00.302792+00:00
-- url     : https://prove2.me/submissions/f5b1b6fd-c84b-48a5-ab2c-49e6c5f3d87c

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_actual_jump_candidates_measurable_dedup

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℕ → Ω → ℝ≥0) (hT : ∀ n, Measurable (T n))
    (hCover : ∀ ω u, 0 < u →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 →
      ∃ n, T n ω = u) :
    let A : ℕ → Set Ω := fun n => {ω |
      0 < T n ω ∧
      X.X (T n ω) ω -
        Function.leftLim (fun u : ℝ≥0 => X.X u ω) (T n ω) ≠ 0 ∧
      ∀ m < n, T m ω ≠ T n ω}
    (∀ n, MeasurableSet (A n)) ∧
    (∀ ω u, 0 < u →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 →
      ∃ n, ω ∈ A n ∧ T n ω = u) := by
  classical
  constructor
  · exact (avram_wave5_02a_actual_jump_candidates_measurable_dedup X T hT).1
  · intro ω u hu hj
    have hex : ∃ n, T n ω = u := hCover ω u hu hj
    let n := Nat.find hex
    have hn : T n ω = u := Nat.find_spec hex
    refine ⟨n, ?_, hn⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa [hn] using hu
    · simpa [hn] using hj
    · intro m hm heq
      exact (Nat.find_min hex hm) (heq.trans hn)
