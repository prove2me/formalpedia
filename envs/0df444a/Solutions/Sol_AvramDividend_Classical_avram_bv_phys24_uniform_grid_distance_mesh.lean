-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_phys24_uniform_grid_distance_mesh
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T22:41:13.436775+00:00
-- url     : https://prove2.me/submissions/085346a1-a1b0-43af-acc8-7372951c5a50

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Topology.Order.OrderClosed
import Theorems.Thm_AvramDividend_Classical_avram_a19_uniform_grid_exact_cell_width
import Theorems.Thm_AvramDividend_Classical_avram_a19_uniform_delta_profile
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2)) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in (atTop : Filter ℕ), ∀ i : ℕ, i < n + 1 →
        dist (u n i) (u n (i + 1)) < ε := by
  intro ε hε
  have hp := AvramDividend.Classical.avram_a19_uniform_delta_profile T hT
  have hlim : Tendsto (fun n : ℕ => T / ((n : ℝ) + 2)) atTop (nhds (0 : ℝ)) :=
    hp.2.2.2
  have hevent : Filter.Eventually
      (fun n : ℕ => T / ((n : ℝ) + 2) < ε) (atTop : Filter ℕ) :=
    hlim.eventually (Iio_mem_nhds hε)
  filter_upwards [hevent] with n hn i hi
  have hw := AvramDividend.Classical.avram_a19_uniform_grid_exact_cell_width
    T hT u huniform n i
  have hnonneg : 0 ≤ (u n (i + 1) : ℝ) - (u n i : ℝ) := by
    rw [hw]
    exact (hp.1 n).le
  rw [NNReal.dist_eq, abs_sub_comm, abs_of_nonneg hnonneg, hw]
  exact hn
