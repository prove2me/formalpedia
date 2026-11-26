-- Prove2me | solution 1 for FirstPassageLinearTransport.shrinkingHighTolerance_sq_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:20:13.941529+00:00
-- url     : https://prove2.me/submissions/c227e183-31f0-4e6b-aea0-0c4fb351bfbf

import Definitions.Def_FirstPassageLinearTransport_ShrinkingProfile
import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_ShrinkingHighDensity
import Theorems.Thm_FirstPassageLinearTransport_shrinkingHighTolerance_eq_formula

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (P : ShrinkingBarrierRunData) {C : ℝ}
    (hC : 0 < C) (hcap : P.D / Real.sqrt C ≤ P.tau)
    {M m : ℕ} (hm : 1 ≤ m)
    (hCm : C * Real.log ((M : ℝ) + 2) ≤ (m : ℝ)) :
    shrinkingHighTolerance P M m ^ 2 * (m : ℝ) =
      P.D ^ 2 * Real.log ((M : ℝ) + 2) := by
  rw [shrinkingHighTolerance_eq_formula P hC hcap hm hCm]
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hx1 : (1 : ℝ) ≤ (M : ℝ) + 2 := by
    linarith
  have hlog0 : 0 ≤ Real.log ((M : ℝ) + 2) := Real.log_nonneg hx1
  rw [mul_pow, Real.sq_sqrt (div_nonneg hlog0 hmR.le)]
  field_simp [ne_of_gt hmR]
end FirstPassageLinearTransport
