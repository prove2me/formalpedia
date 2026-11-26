-- Prove2me | solution 1 for Eden.log_add_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:30:53.938798+00:00
-- url     : https://prove2.me/submissions/c74b039c-8b17-4a34-b6cc-b283eedec35a

import Definitions.Def_Eden_RealTimeAverages
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_Eden_LogarithmicSums

set_option autoImplicit true
noncomputable section
open Filter Set
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    max (Real.log x) (Real.log y) ≤ Real.log (x + y) ∧
      Real.log (x + y) ≤ Real.log 2 + max (Real.log x) (Real.log y) := by
  have hlow : max (Real.log x) (Real.log y) ≤ Real.log (x + y) :=
    max_le (Real.log_le_log hx (by linarith)) (Real.log_le_log hy (by linarith))
  refine ⟨hlow, ?_⟩
  rcases le_total x y with h | h
  · rw [max_eq_right (Real.log_le_log hx h)]
    calc
      Real.log (x + y) ≤ Real.log (2 * y) := Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 2 + Real.log y := Real.log_mul (by norm_num) hy.ne'
  · rw [max_eq_left (Real.log_le_log hy h)]
    calc
      Real.log (x + y) ≤ Real.log (2 * x) := Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 2 + Real.log x := Real.log_mul (by norm_num) hx.ne'
end Eden
