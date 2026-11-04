-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_h_cadlag_uniform_grid_no_spurious_large_cell_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:12:38.409617+00:00
-- url     : https://prove2.me/submissions/b8397587-bc09-43b9-824c-17d5925540f4

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_positive_uniform_mesh_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_horizon_coverage
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_uniform_right_closed_cell_real_width
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_eventually_all_large_fine_cells_contain_actual_jumps

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology AvramDividend.Classical
open scoped NNReal

/-- All sufficiently fine original uniform right-closed cells with
large real increments contain a genuine jump of that magnitude. -/
theorem solution
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0) (hT : 0 < T)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hL : ∀ t, t ≤ T →
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ∀ t, t ≤ T → ContinuousWithinAt Y (Ici t) t) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ i : ℕ, i ≤ n →
      ρ ≤ |Y ((((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))) -
        Y (((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))))| →
      ∃ t : ℝ≥0,
        ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) < t ∧
        t ≤ (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ∧
        ρ ≤ |Y t - Function.leftLim Y t| := by
  let δ : ℕ → ℝ≥0 := fun n => T / ((n : ℝ≥0) + 1)
  let a : ℕ → ℕ → ℝ≥0 := fun n i => ((min i n : ℕ) : ℝ≥0) * δ n
  let b : ℕ → ℕ → ℝ≥0 := fun n i =>
    (((min i n + 1 : ℕ) : ℝ≥0) * δ n)
  have hab : ∀ n i, a n i ≤ b n i := by
    intro n i
    dsimp [a, b]
    gcongr
    exact Nat.le_succ _
  have hbound : ∀ n i, b n i ≤ T := by
    intro n i
    calc
      b n i ≤ ((n : ℝ≥0) + 1) * δ n := by
        dsimp [b]
        gcongr
        exact_mod_cast (Nat.succ_le_succ (Nat.min_le_right i n))
      _ = T := avram_p2_a_zero_rate_uniform_horizon_coverage T n
  have hbase : Tendsto (fun n : ℕ => (T : ℝ) / ((n : ℝ) + 1))
      atTop (𝓝 (0 : ℝ)) :=
    tendsto_nhds_of_tendsto_nhdsWithin
      (avram_p2_a_zero_rate_positive_uniform_mesh_tendsto T hT)
  have hwidth : ∀ (is ns : ℕ → ℕ),
      Tendsto ns atTop (atTop : Filter ℕ) →
      Tendsto (fun k => (b (ns k) (is k) : ℝ) -
        (a (ns k) (is k) : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    intro is ns hns
    have heq : (fun k => (b (ns k) (is k) : ℝ) -
        (a (ns k) (is k) : ℝ)) =
        (fun k => (T : ℝ) / ((ns k : ℝ) + 1)) := by
      funext k
      exact avram_p2_h_cadlag_uniform_right_closed_cell_real_width
        T (ns k) (min (is k) (ns k))
    rw [heq]
    exact hbase.comp hns
  obtain ⟨N, hN⟩ :=
    avram_p2_h_cadlag_eventually_all_large_fine_cells_contain_actual_jumps
      Y T ρ hρ a b hab hbound hwidth hL hR
  refine ⟨N, ?_⟩
  intro n hn i hi hlarge
  have hlarge' : ρ ≤ |Y (b n i) - Y (a n i)| := by
    simpa only [a, b, δ, Nat.min_eq_left hi] using hlarge
  simpa only [a, b, δ, Nat.min_eq_left hi] using hN n hn i hlarge'
