-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.bordered_pos_of_fiber
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-29T22:45:25.260987+00:00
-- url     : https://prove2.me/submissions/abfadd0c-bc65-49e0-a4f0-e5919045c400

import Definitions.Def_BirkhoffGlobalSection_TangentialHessian_Fiber
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_bordered_kHessR_block
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_fiber_trig_pos
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_K_eq_fiber
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_kHessR_fiber_blocks
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp

open Matrix in
open BirkhoffGlobalSection BirkhoffGlobalSection.TangentialHessian in
theorem solution (μ c r : ℝ) (s : Phase)
    (hK : pP μ c s - μ * (zNormSq s / r) = 0)
    (hG : 0 < fibG μ c r s)
    (hW : fibF μ c r s * (fibBeta1 μ c r s ^ 2 + fibBeta2 μ c r s ^ 2) < fibG μ c r s ^ 2) :
    0 < kGradR μ c r s ⬝ᵥ (kHessR μ c r s).adjugate.mulVec (kGradR μ c r s) := by
  obtain ⟨e00, e11, e01, ev0, ev1⟩ := kHessR_fiber_blocks μ c r s
  have hc : kGradR μ c r s 2 ^ 2 + kGradR μ c r s 3 ^ 2 = fibF μ c r s := by
    have := K_eq_fiber μ c r s; linarith
  rw [bordered_kHessR_block, e00, e11, e01, ev0, ev1]
  have hZ : zNormSq s = s 0 ^ 2 + s 1 ^ 2 := rfl
  unfold fibG at hG hW
  unfold fibBeta1 fibBeta2 at hW
  rw [hZ] at hG hW
  exact fiber_trig_pos _ _ _ _ _ _ _ _ (s 0) (s 1) hc hG hW
