-- Prove2me | solution 1 for D1Bound5.exists_root_error_three
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:22:22.679181+00:00
-- url     : https://prove2.me/submissions/f81f2c2b-968a-48b7-8d23-6dceaf1c98c4

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theorems.Thm_D1Bound5_exists_root_error_control

section
namespace D1Bound5








/-- First-row entries in the A >= 1, B >= 3 determinant argument. -/
theorem _root_.solution (x t : ℂ)
    (hx : 3 ≤ ‖x‖) (ht : t^2 = x*(x+1)) :
    ∃ v : ℂ, (v=t ∨ v=-t) ∧
      ‖v-x‖ < (5/9 : ℝ) ∧
      ‖(v-x)-(1/2 : ℂ)‖ < (25/486 : ℝ) := by
  have hxpos : 0 < ‖x‖ := by linarith
  have hgap : 1 < (1-(4/5 : ℝ)^2)*‖x‖ := by nlinarith only [hx]
  obtain ⟨v,hv,hnear,hhalf⟩ :=
    exists_root_error_control x t (4/5) (by norm_num) hxpos hgap ht
  have hnear' : ‖v-x‖ < (5/9 : ℝ) := by nlinarith only [hnear]
  have hprod := mul_nonneg (sub_nonneg.mpr hx)
    (norm_nonneg ((v-x)-(1/2 : ℂ)))
  have hhalf' : ‖(v-x)-(1/2 : ℂ)‖ < (25/486 : ℝ) := by
    nlinarith only [hhalf,hprod]
  exact ⟨v,hv,hnear',hhalf'⟩



end D1Bound5
end
