-- Prove2me | solution 1 for FractionalCalc.scottBlair_creep
-- status  : ACCEPTED   (prove)
-- author  : @Yivy Yu
-- created : 2026-11-23T02:10:36.938898+00:00
-- url     : https://prove2.me/submissions/2ffc73aa-3368-46bc-9fd2-e75718634520

import Definitions.Def_FractionalCalc_scottBlair

open MeasureTheory Set FractionalCalc

/-- The memory-kernel integral, including the singular exponents between -1 and 0. -/
private theorem memoryKernel_integral (α t : ℝ) (hα : 0 < α) (ht : 0 < t) :
    (∫ u in Ioo 0 t, (t - u) ^ (α - 1)) = t ^ α / α := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ht.le]
  rw [intervalIntegral.integral_comp_sub_left (fun u : ℝ => u ^ (α - 1)) t]
  simp only [sub_self, sub_zero]
  rw [integral_rpow (Or.inl (by linarith : -1 < α - 1))]
  rw [sub_add_cancel, Real.zero_rpow (ne_of_gt hα), sub_zero]

/-- Fractional integration of a unit step gives the power-law creep compliance. -/
theorem solution (E τ α : ℝ) (t : ℝ)
    (_hE : 0 < E) (_hτ : 0 < τ) (hα : 0 < α) (ht : 0 < t) :
    scottBlairCreep E τ α t = t ^ α / (E * τ ^ α * Real.Gamma (1 + α)) := by
  have hαne : α ≠ 0 := ne_of_gt hα
  have hstep : (∫ u in Ioo 0 t, (t - u) ^ (α - 1) * heaviside u) =
      ∫ u in Ioo 0 t, (t - u) ^ (α - 1) := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro u hu
    simp only [heaviside, if_pos hu.1, mul_one]
  unfold scottBlairCreep rlIntegral
  rw [if_neg hαne, hstep, memoryKernel_integral α t hα ht]
  have hgamma : Real.Gamma (1 + α) = α * Real.Gamma α := by
    simpa only [add_comm] using Real.Gamma_add_one hαne
  rw [hgamma]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring
