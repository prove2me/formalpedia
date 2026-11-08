-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_jump8_turn9_measurable_exact_cadlag_selectors
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T08:56:24.386714+00:00
-- url     : https://prove2.me/submissions/6a0fd8ee-1440-4317-ba77-d8864df922d1

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Topology.Order.LeftRightLim
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_two_sign_cadlag_measurable_candidate_time_enumeration
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_dense_grid_all_candidate_exact_marked_Borel_series
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Fixed dense clock and countable rational thresholds give exact measurable marks. -/
theorem solution :
    ∃ (time : ℕ → (ℝ≥0 → ℝ) → ℝ≥0)
      (mark : ℕ → (ℝ≥0 → ℝ) → ℝ),
      (∀ k, Measurable (time k)) ∧
      (∀ k, Measurable (mark k)) ∧
      ∀ Y : ℝ≥0 → ℝ,
        (∀ u : ℝ≥0, ContinuousWithinAt Y (Ici u) u) →
        (∀ u : ℝ≥0, 0 < u → ∃ l : ℝ, Tendsto Y (𝓝[<] u) (𝓝 l)) →
        (∀ k : ℕ, 0 < time k Y →
          mark k Y = Y (time k Y) - Function.leftLim Y (time k Y)) ∧
        (∀ u : ℝ≥0, 0 < u → Y u - Function.leftLim Y u ≠ 0 →
          ∃ k : ℕ, time k Y = u) := by
  classical
  obtain ⟨grid, hdense⟩ :
      ∃ grid : ℕ → ℝ≥0, DenseRange grid :=
    TopologicalSpace.exists_dense_seq ℝ≥0
  obtain ⟨pairs, hpairs⟩ :
      ∃ pairs : ℕ → ℕ × ℚ, Function.Surjective pairs :=
    exists_surjective_nat (ℕ × ℚ)
  let ε : ℕ → ℝ≥0 := fun n => 1 / (n + 1)
  have hεpos (n : ℕ) : 0 < ε n := by
    simp [ε]
  have hε : Tendsto ε atTop (𝓝 0) := by
    simpa [ε] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ≥0))
  obtain ⟨time, hTimeMeas, hCover⟩ :=
    avram_wave7_01_two_sign_cadlag_measurable_candidate_time_enumeration
      grid hdense pairs hpairs
  obtain ⟨mark, hMarkMeas, hExact, _⟩ :=
    avram_wave7_01_dense_grid_all_candidate_exact_marked_Borel_series
      grid hdense time hTimeMeas ε hεpos hε 0 Set.univ MeasurableSet.univ
  refine ⟨time, mark, hTimeMeas, hMarkMeas, ?_⟩
  intro Y hRight hLeft
  have hLeftExact :
      ∀ u : ℝ≥0, 0 < u →
        Tendsto Y (𝓝[<] u) (𝓝 (Function.leftLim Y u)) := by
    intro u hu
    obtain ⟨l, hl⟩ := hLeft u hu
    letI : NeBot (𝓝[<] u) :=
      nhdsLT_neBot_of_exists_lt ⟨0, hu⟩
    have heq : Function.leftLim Y u = l :=
      leftLim_eq_of_tendsto hl
    simpa only [heq] using hl
  constructor
  · intro k hpos
    exact hExact k Y hpos (hRight (time k Y))
      (hLeftExact (time k Y) hpos)
  · intro u hu hjump
    exact hCover Y hRight hLeftExact u hu hjump
