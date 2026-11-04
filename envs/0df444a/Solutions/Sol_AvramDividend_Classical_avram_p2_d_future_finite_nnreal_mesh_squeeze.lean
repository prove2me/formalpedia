-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_d_future_finite_nnreal_mesh_squeeze
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:07:38.438551+00:00
-- url     : https://prove2.me/submissions/6c062aef-a60a-4745-a0b3-f2d1dbe0fce9

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_nnreal_finite_rate_grid_step_arbitrarily_small

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Rational mesh bounds with finite nonnegative slope uniquely determine
the exact value at every real horizon by an Archimedean squeeze. -/
theorem solution
    (c t m : ℝ≥0)
    (hmesh : ∀ d : ℕ, 0 < d → ∃ n : ℕ,
      ((n : ℝ≥0) / (d : ℝ≥0)) ≤ t ∧
      t ≤ (((n + 1 : ℕ) : ℝ≥0) / (d : ℝ≥0)) ∧
      ((n : ℝ≥0) / (d : ℝ≥0)) * c ≤ m ∧
      m ≤ (((n + 1 : ℕ) : ℝ≥0) / (d : ℝ≥0)) * c) :
    m = t * c := by
  have hbound (ε : ℝ≥0) (hε : 0 < ε) :
      m ≤ t * c + ε ∧ t * c ≤ m + ε := by
    obtain ⟨d, hd, hsmall⟩ :=
      avram_p2_d_future_nnreal_finite_rate_grid_step_arbitrarily_small c ε hε
    obtain ⟨n, hlt, hgt, hlo, hhi⟩ := hmesh d hd
    have hcell :
        (((n + 1 : ℕ) : ℝ≥0) / (d : ℝ≥0)) =
          ((n : ℝ≥0) / (d : ℝ≥0)) + (1 / (d : ℝ≥0)) := by
      push_cast
      rw [add_div]
    have hstep :
        (((n + 1 : ℕ) : ℝ≥0) / (d : ℝ≥0)) * c =
          ((n : ℝ≥0) / (d : ℝ≥0)) * c + c / (d : ℝ≥0) := by
      rw [hcell, add_mul]
      congr 1
      ring
    have hupper : m ≤ t * c + c / (d : ℝ≥0) := by
      calc
        m ≤ (((n + 1 : ℕ) : ℝ≥0) / (d : ℝ≥0)) * c := hhi
        _ = ((n : ℝ≥0) / (d : ℝ≥0)) * c + c / (d : ℝ≥0) := hstep
        _ ≤ t * c + c / (d : ℝ≥0) := by gcongr
    have hlower : t * c ≤ m + c / (d : ℝ≥0) := by
      calc
        t * c ≤ (((n + 1 : ℕ) : ℝ≥0) / (d : ℝ≥0)) * c := by gcongr
        _ = ((n : ℝ≥0) / (d : ℝ≥0)) * c + c / (d : ℝ≥0) := hstep
        _ ≤ m + c / (d : ℝ≥0) := by gcongr
    exact ⟨le_trans hupper (add_le_add_right hsmall.le _),
      le_trans hlower (add_le_add_right hsmall.le _)⟩
  have hmle : (m : ℝ≥0∞) ≤ ((t * c : ℝ≥0) : ℝ≥0∞) := by
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    exact_mod_cast (hbound ε hε).1
  have htle : ((t * c : ℝ≥0) : ℝ≥0∞) ≤ (m : ℝ≥0∞) := by
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    exact_mod_cast (hbound ε hε).2
  exact_mod_cast (le_antisymm hmle htle)
