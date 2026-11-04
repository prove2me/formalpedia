-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_selected_right_endpoint_squeeze
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:20:06.727959+00:00
-- url     : https://prove2.me/submissions/45a83421-df29-4c7f-8f22-69c69f8ff388

import Mathlib.Topology.Order.Basic
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_cell_increment_to_jump
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology
open scoped NNReal

/-- A selected original mesh right endpoint squeezed between a genuine
jump time and that time plus vanishing mesh width converges to the jump. -/
theorem solution
    (u : ℝ≥0) (r w : ℕ → ℝ≥0)
    (hr : ∀ n, u ≤ r n ∧ r n ≤ u + w n)
    (hw : Tendsto w atTop (𝓝 (0 : ℝ≥0))) :
    Tendsto r atTop (𝓝 u) := by
  have hlo : Tendsto (fun _ : ℕ => u) atTop (𝓝 u) :=
    tendsto_const_nhds
  have hhi : Tendsto (fun n : ℕ => u + w n) atTop (𝓝 u) := by
    simpa using hlo.add hw
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    hlo hhi (fun n => (hr n).1) (fun n => (hr n).2)
