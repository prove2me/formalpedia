-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.tHess_det_pos
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-29T22:45:31.28552+00:00
-- url     : https://prove2.me/submissions/f8dc7fb7-afd5-4fd7-87e3-fee0060c6f18

import Definitions.Def_BirkhoffGlobalSection_TangentialHessian_Fiber
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_fiber_gate_pos
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_tHess_det_pos_of_fiber
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_K_eq_fiber
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp

open BirkhoffGlobalSection BirkhoffGlobalSection.TangentialHessian in
theorem solution (μ c r : ℝ) (s : Phase)
    (hμ0 : 0 ≤ μ) (hμhalf : μ ≤ 1 / 2)
    (hc0 : 21 / 10 ≤ c) (hc1 : c ≤ 21 / 10 + 1 / 1000000)
    (hr : 0 < r) (hr2 : r ^ 2 = secondCollisionDistanceSq s)
    (hK : pP μ c s - μ * (zNormSq s / r) = 0)
    (hz : 2 * zNormSq s ≤ (3 - 2 * μ) / 5) (_hw : wNormSq s ≤ 4) :
    0 < (tHessR μ c r s).det := by
  have hF : 0 ≤ fibF μ c r s := by
    have h := K_eq_fiber μ c r s
    nlinarith [sq_nonneg (kGradR μ c r s 2), sq_nonneg (kGradR μ c r s 3)]
  obtain ⟨hG, hW⟩ := fiber_gate_pos μ c r s hμ0 hμhalf hc0 hc1 hr hr2 hz hF
  exact tHess_det_pos_of_fiber μ c r s hμ0 hμhalf hc0 hc1 hr hr2 hK hz hG hW
