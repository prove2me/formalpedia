-- Prove2me | solution 1 for Eden.singularWeight_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:03:42.204182+00:00
-- url     : https://prove2.me/submissions/1bc98764-bb44-4ff6-a77b-072f86135c73

import Definitions.Def_Eden_KaplanYorke
import Definitions.Def_Eden_SingularValueFunction
import Mathlib.Topology.MetricSpace.UniformConvergence
import Definitions.Def_Eden_LogarithmicInterpolation

set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution (i : ℕ) (d : ℝ) :
    0 ≤ singularWeight i d ∧ singularWeight i d ≤ 1 := by
  exact ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩
end Eden
