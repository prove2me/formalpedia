-- Prove2me | solution 1 for Eden.singularWeight_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:41:17.992271+00:00
-- url     : https://prove2.me/submissions/ea5e691e-9444-4b1f-a553-108e548b9d12

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
theorem _root_.solution {i k : ℕ} (hki : k < i) {α : ℝ} (hα : α ≤ 1) :
    singularWeight i ((k : ℝ) + α) = 0 := by
  have hi : (k : ℝ) + 1 ≤ i := by exact_mod_cast hki
  unfold singularWeight
  rw [max_eq_left (by linarith)]
  norm_num
end Eden
