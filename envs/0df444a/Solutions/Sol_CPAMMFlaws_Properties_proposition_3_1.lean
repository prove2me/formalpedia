-- Prove2me | solution 1 for CPAMMFlaws.Properties.proposition_3_1
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-16T08:27:27.742589+00:00
-- url     : https://prove2.me/submissions/87458e10-81e5-4f4e-93a5-d1b89f96d487

import Mathlib
import Definitions.Def_CPAMMFlaws_Properties_Setting
open CPAMMFlaws.Properties

theorem solution(X Y x α : ℝ) (hX : 0 < X) (hY : 0 < Y)
    (hx : 0 < x) (hxX : x < X) (hα : 0 < α) (hα1 : α < 1) :
    pcmm (α * x) X Y + pcmm ((1 - α) * x) (X - α * x) (Y + pcmm (α * x) X Y) =
      pcmm x X Y := by
  have hax : α * x < x := by nlinarith
  have h1 : X - α * x ≠ 0 := by linarith
  have h3 : X - x ≠ 0 := by linarith
  unfold pcmm
  rw [show X - α * x - (1 - α) * x = X - x by ring]
  field_simp
  ring
