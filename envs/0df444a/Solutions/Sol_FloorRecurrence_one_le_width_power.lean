-- Prove2me | solution 1 for FloorRecurrence.one_le_width_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.154279+00:00
-- url     : https://prove2.me/submissions/a1a1185c-ce13-45d9-9fe2-08d2f6f55dd7

import Definitions.Def_FloorDepth
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_FloorRecurrence

set_option autoImplicit true
open FloorRecurrence
open scoped BigOperators
namespace FloorRecurrence
theorem _root_.solution (e : ℕ) (p : ℝ) (he : 0 < e) (hp : 0 ≤ p) :
    1 ≤ (e : ℝ) ^ p := by
  have heR : (1 : ℝ) ≤ e := by exact_mod_cast he
  simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) heR hp
end FloorRecurrence
