-- Prove2me | solution 1 for Eden.q_expansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:04:25.852131+00:00
-- url     : https://prove2.me/submissions/6a4c181b-de55-4b92-8562-886e4091f71d

import Definitions.Def_Eden_Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Eden_Algebra

set_option autoImplicit true
open Eden
namespace Eden
theorem _root_.solution (s : ℝ) : q s = -s ^ 2 + 3 * s - 2 := by
  unfold q
  ring
end Eden
