-- Prove2me | solution 1 for Eden.singularWeight_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:24:03.762848+00:00
-- url     : https://prove2.me/submissions/ab353841-cee3-4c72-81f5-108ae983e7ef

import Definitions.Def_Eden_SingularValues
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Compact
import Definitions.Def_Eden_SingularValueFunction

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {i k : ℕ} (hik : i < k) {α : ℝ} (hα : 0 ≤ α) :
    singularWeight i ((k : ℝ) + α) = 1 := by
  have hi : (i : ℝ) + 1 ≤ k := by exact_mod_cast hik
  unfold singularWeight
  rw [max_eq_right (by linarith), min_eq_left (by linarith)]
end Eden
