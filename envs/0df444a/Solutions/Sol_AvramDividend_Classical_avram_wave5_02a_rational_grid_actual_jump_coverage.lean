-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_02a_rational_grid_actual_jump_coverage
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:51:56.371675+00:00
-- url     : https://prove2.me/submissions/00aacd51-017b-4867-b38d-33d4053fccbe

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_actual_source_countable_grid_first_hit_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_actual_source_jump_rational_separation
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_dense_grid_recovers_separated_source_jump

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (grid : ℕ → ℝ≥0) (hdense : DenseRange grid)
    (pairs : ℕ → ℕ × ℚ) (hpairs : Function.Surjective pairs) :
    let T : ℕ → Ω → ℝ≥0 := fun k ω =>
      (⨅ n : ℕ, {ω : Ω | grid (pairs k).1 < grid n ∧
          X.X (grid n) ω < ((pairs k).2 : ℝ)}.piecewise
        (fun _ => (grid n : ℝ≥0∞)) (fun _ => ⊤) ω).toNNReal
    (∀ k, Measurable (T k)) ∧
    (∀ ω u, 0 < u →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 →
      ∃ k, T k ω = u) := by
  constructor
  · intro k
    exact ENNReal.measurable_toNNReal.comp
      (avram_wave5_02a_actual_source_countable_grid_first_hit_measurable
        X grid (grid (pairs k).1) ((pairs k).2 : ℝ))
  · intro ω u hu hj
    obtain ⟨a, s, b, hsu, hub, hL, hR⟩ :=
      avram_wave5_02a_actual_source_jump_rational_separation X ω u hu hj
    obtain ⟨m, hm, hI⟩ :=
      avram_wave5_02a_dense_grid_recovers_separated_source_jump
        X ω grid hdense s u b (a : ℝ) hsu hub hL hR
    obtain ⟨k, hk⟩ := hpairs (m, a)
    refine ⟨k, ?_⟩
    dsimp
    rw [hk]
    simpa only [ENNReal.toNNReal_coe] using congrArg ENNReal.toNNReal hI
