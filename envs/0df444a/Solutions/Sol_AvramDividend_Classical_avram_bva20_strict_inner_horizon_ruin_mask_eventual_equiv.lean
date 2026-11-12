-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva20_strict_inner_horizon_ruin_mask_eventual_equiv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T20:49:45.796432+00:00
-- url     : https://prove2.me/submissions/6f87374b-d1c0-4bbc-bc36-ab9dc0f93c9e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_uniform_strict_mesh_cofinal_at_horizon

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Away from ruin the inner-horizon inclusive mask stabilises to strict pre-ruin. -/
theorem solution
    (T : ℝ) (hT : 0 < T) (τ : ℝ≥0∞)
    (t : ℝ) (ht0 : 0 < t) (htT : t < T)
    (hτ : ENNReal.ofReal t ≠ τ) :
    Filter.Eventually
      (fun n : ℕ =>
        (0 < t ∧ t < T - T / ((n : ℝ) + 2) ∧
          ENNReal.ofReal t ≤ τ) ↔
        (0 < t ∧ ENNReal.ofReal t < τ))
      Filter.atTop := by
  have hlimit :=
    (avram_p3_grid4_original_uniform_strict_mesh_cofinal_at_horizon T hT).2
  have he : ∀ᶠ n : ℕ in atTop, t < T - T / ((n : ℝ) + 2) :=
    hlimit.eventually (Ioi_mem_nhds htT)
  filter_upwards [he] with n hn
  constructor
  · intro h
    exact ⟨h.1, lt_of_le_of_ne h.2.2 hτ⟩
  · intro h
    exact ⟨h.1, hn, le_of_lt h.2⟩
