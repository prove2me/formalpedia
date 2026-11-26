-- Prove2me | solution 1 for Eden.targetDimension_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:19:09.969156+00:00
-- url     : https://prove2.me/submissions/e9fd2944-252b-4682-bd24-e23c751cf0fe

import Definitions.Def_Eden_Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Eden_Algebra

set_option autoImplicit true
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c) :
    4 < targetDimension c ∧ targetDimension c < 5 := by
  have hc₀ : 0 < c := by linarith
  have hpos : 0 < (4 : ℝ) / c := div_pos (by norm_num) hc₀
  have hlt : (4 : ℝ) / c < 1 := (div_lt_one hc₀).2 hc
  dsimp [targetDimension]
  constructor <;> linarith
end Eden
