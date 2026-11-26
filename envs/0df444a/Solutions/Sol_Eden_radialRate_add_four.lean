-- Prove2me | solution 1 for Eden.radialRate_add_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:04:41.906885+00:00
-- url     : https://prove2.me/submissions/4b684b2f-47f3-43cc-b65f-69e9fb22b59f

import Definitions.Def_Eden_Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Eden_Algebra

set_option autoImplicit true
open Eden
namespace Eden
theorem _root_.solution (s : ℝ) :
    radialRate s + 4 = (2 - s) * (5 * s + 1) := by
  unfold radialRate
  ring
end Eden
