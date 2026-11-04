-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_frequently_bad_source_grid_cells_impossible
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:44:20.268413+00:00
-- url     : https://prove2.me/submissions/89886ec0-ea35-444e-82dd-19006a3352a9

import Mathlib.Topology.Order.LeftRightLim
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_finite_actual_jumps_exclude_spurious_large_cells
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology AvramDividend.Classical
open scoped NNReal

theorem solution
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0)
    (a b : ℕ → ℕ → ℝ≥0) (w : ℕ → ℝ≥0)
    (haT : ∀ n i, a n i ≤ T)
    (hab : ∀ n i, a n i ≤ b n i)
    (hbw : ∀ n i, b n i ≤ a n i + w n)
    (hw : Tendsto w atTop (𝓝 (0 : ℝ≥0)))
    (hL : ∀ t : ℝ≥0,
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ∀ t : ℝ≥0, ContinuousWithinAt Y (Ici t) t)
    (ρ : ℝ) (hρ : 0 < ρ)
    (F : Finset ℝ≥0)
    (hF : ∀ t ∈ Icc (0 : ℝ≥0) T,
       ρ ≤ |Y t - Function.leftLim Y t| → t ∈ F)
    (havoid : ∀ n i, ∀ t ∈ F, ¬ (a n i < t ∧ t ≤ b n i))
    (hbad : ∃ᶠ n in (atTop : Filter ℕ),
      ∃ i, ρ ≤ |Y (b n i) - Y (a n i)|) :
    False := by
  obtain ⟨φ, hφ, hbadφ⟩ :=
    Filter.exists_seq_forall_of_frequently hbad
  let j : ℕ → ℕ := fun n => Classical.choose (hbadφ n)
  have hlarge : ∀ n,
      ρ ≤ |Y (b (φ n) (j n)) - Y (a (φ n) (j n))| := by
    intro n
    exact Classical.choose_spec (hbadφ n)
  exact avram_p2_a_zero_rate_finite_actual_jumps_exclude_spurious_large_cells
    Y T (fun n => a (φ n) (j n)) (fun n => b (φ n) (j n))
    (fun n => w (φ n)) (fun n => haT (φ n) (j n))
    (fun n => hab (φ n) (j n))
    (fun n => hbw (φ n) (j n))
    (hw.comp hφ) hL hR ρ hρ F hF
    (fun n t ht => havoid (φ n) (j n) t ht) hlarge
