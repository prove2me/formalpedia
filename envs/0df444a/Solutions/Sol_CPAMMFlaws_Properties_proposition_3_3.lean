-- Prove2me | solution 1 for CPAMMFlaws.Properties.proposition_3_3
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-16T08:26:04.277351+00:00
-- url     : https://prove2.me/submissions/d6c59595-a86a-46b0-ae21-28bb6c148081

import Mathlib
import Definitions.Def_CPAMMFlaws_Properties_Setting
open CPAMMFlaws.Properties

theorem solution(X Y x k : ℝ) (hX : 0 < X) (hY : 0 < Y)
    (hx : 0 < x) (hxX : x < X) (hk : 0 < k) :
    pcmm x X Y = k * pcmm (x / k) (X / k) (Y / k) := by
  have h : X - x ≠ 0 := by linarith
  have hk' : k ≠ 0 := hk.ne'
  unfold pcmm
  rw [show X / k - x / k = (X - x) / k by ring]
  field_simp
