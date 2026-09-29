-- Prove2me | solution 1 for AvgCompletionSched.BestAlpha.exp_density_delta
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:58:07.857935+00:00
-- url     : https://prove2.me/submissions/f7794eb2-ba93-496b-80ee-df791c6363bb

import Mathlib
import Definitions.Def_AvgCompletionSched_BestAlpha_Model

namespace AvgCompletionSched.BestAlpha

theorem aux_edd_hasDeriv (β c : ℝ) (x : ℝ) :
    HasDerivAt (fun α : ℝ => (α - β) * Real.exp α / (β * c))
      ((1 + x - β) / β * (Real.exp x / c)) x := by
  have h1 : HasDerivAt (fun α : ℝ => α - β) 1 x := (hasDerivAt_id x).sub_const β
  have h2 := h1.mul (Real.hasDerivAt_exp x)
  have h3 := h2.div_const (β * c)
  have e : (1 * Real.exp x + (x - β) * Real.exp x) / (β * c)
      = (1 + x - β) / β * (Real.exp x / c) := by
    rw [div_mul_div_comm]
    congr 1
    ring
  exact e ▸ h3

end AvgCompletionSched.BestAlpha

open AvgCompletionSched.BestAlpha

theorem solution :
    (∀ α : ℝ, 0 ≤ Real.exp α / (Real.exp 1 - 1)) ∧
      ∫ α in (0 : ℝ)..1, Real.exp α / (Real.exp 1 - 1) = 1 ∧
      ∀ β ∈ Set.Ioc (0 : ℝ) 1,
        ∫ α in (0 : ℝ)..β, (1 + α - β) / β * (Real.exp α / (Real.exp 1 - 1))
          = 1 / (Real.exp 1 - 1) := by
  have he : (1 : ℝ) < Real.exp 1 := by
    have := Real.add_one_lt_exp (x := (1:ℝ)) one_ne_zero
    linarith
  have hc : 0 < Real.exp 1 - 1 := by linarith
  refine ⟨fun α => div_nonneg (Real.exp_pos α).le hc.le, ?_, ?_⟩
  · rw [intervalIntegral.integral_div, integral_exp, Real.exp_zero]
    exact div_self hc.ne'
  · intro β hβ
    have hβ0 : 0 < β := hβ.1
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun α : ℝ => (α - β) * Real.exp α / (β * (Real.exp 1 - 1)))
      (fun x _ => aux_edd_hasDeriv β (Real.exp 1 - 1) x)]
    · simp only [sub_self, zero_mul, zero_div, zero_sub, Real.exp_zero, mul_one]
      field_simp
    · apply Continuous.intervalIntegrable
      fun_prop
