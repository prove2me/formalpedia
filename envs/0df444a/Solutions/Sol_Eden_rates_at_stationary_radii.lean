-- Prove2me | solution 1 for Eden.rates_at_stationary_radii
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:05:38.152083+00:00
-- url     : https://prove2.me/submissions/3971b476-acfe-49c0-b6cb-19e2d79e1f06

import Definitions.Def_Eden_Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Eden_Algebra

set_option autoImplicit true
open Eden
namespace Eden
theorem _root_.solution :
    radialRate 0 = -2 ∧ tangentialRate 0 = -2 ∧
    radialRate 1 = 2 ∧ tangentialRate 1 = 0 ∧
    radialRate 2 = -4 ∧ tangentialRate 2 = 0 := by
  norm_num [radialRate, tangentialRate]
end Eden
