-- Prove2me | solution 1 for CPAMMFlaws.Properties.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-16T08:26:02.6161+00:00
-- url     : https://prove2.me/submissions/947a6387-7767-4d04-bb76-a55671c9a022

import Mathlib
import Definitions.Def_CPAMMFlaws_Properties_Setting
open CPAMMFlaws.Properties

theorem solution(X Y x : ℝ) (hX : 0 < X) (hY : 0 < Y) (hxX : x < X) :
    (∀ y : ℝ, (X - x) * (Y + y) = X * Y ↔ y = pcmm x X Y) ∧
      Y + pcmm x X Y = X * Y / (X - x) := by
  have h : X - x ≠ 0 := by linarith
  unfold pcmm
  refine ⟨fun y => ⟨fun hy => ?_, fun hy => ?_⟩, ?_⟩
  · rw [eq_div_iff h]
    linear_combination hy
  · rw [hy]
    field_simp
    ring
  · field_simp
    ring
