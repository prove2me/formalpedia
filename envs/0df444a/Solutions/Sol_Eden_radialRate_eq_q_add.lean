-- Prove2me | solution 1 for Eden.radialRate_eq_q_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:27:53.162429+00:00
-- url     : https://prove2.me/submissions/3157e2bd-871a-44a4-b631-c8d54867bb00

import Definitions.Def_Eden_Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Eden_Algebra

set_option autoImplicit true
open Eden
namespace Eden
theorem _root_.solution (s : ℝ) :
    radialRate s = q s + 2 * s * (-2 * s + 3) := by
  unfold radialRate q
  ring
end Eden
