-- Prove2me | solution 1 for AvramDividend.Classical.causal_full_kernel_continuousOn_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T07:27:10.684875+00:00
-- url     : https://prove2.me/submissions/c678cb68-eebd-43c7-958d-17a3462a7882

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_continuousOn_positive_of_Ici_input
import Theorems.Thm_AvramDividend_Classical_causal_continuous_input_primitive_continuousOn_nonnegative
import Theorems.Thm_AvramDividend_Classical_causal_l1_kernel_continuous_input_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- A constant drift plus a positive-lag L1 kernel gives a continuous causal operator. -/
theorem solution (K V : ℝ → ℝ) (β : ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hV : ContinuousOn V (Ici (0 : ℝ))) :
    ContinuousOn (fun x : ℝ =>
      ∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) * V s ∂volume)
      (Ioi (0 : ℝ)) := by
  have hp : ContinuousOn (fun x : ℝ =>
      ∫ s in Ioc (0 : ℝ) x, V s ∂volume) (Ioi (0 : ℝ)) :=
    (causal_continuous_input_primitive_continuousOn_nonnegative V hV).mono
      (by intro x hx; change 0 < x at hx; exact le_of_lt hx)
  have hc : ContinuousOn (fun x : ℝ =>
      β * (∫ s in Ioc (0 : ℝ) x, V s ∂volume)) (Ioi (0 : ℝ)) :=
    continuousOn_const.mul hp
  have hk := causal_l1_convolution_continuousOn_positive_of_Ici_input
    K V hK hV
  apply (hc.add hk).congr
  intro x hx
  change 0 < x at hx
  symm
  have hv : IntegrableOn V (Ioc (0 : ℝ) x) volume := by
    have hi : ContinuousOn V (Icc (0 : ℝ) x) :=
      hV.mono (by intro s hs; exact hs.1)
    exact hi.integrableOn_Icc.mono_set
      (by intro s hs; exact ⟨le_of_lt hs.1, hs.2⟩)
  have hki := causal_l1_kernel_continuous_input_integrable K V hK hV x hx
  calc
    β * (∫ s in Ioc (0 : ℝ) x, V s ∂volume) +
        (∫ s in Ioc (0 : ℝ) x, K (x - s) * V s ∂volume) =
        (∫ s in Ioc (0 : ℝ) x, β * V s ∂volume) +
        (∫ s in Ioc (0 : ℝ) x, K (x - s) * V s ∂volume) := by
          rw [integral_const_mul]
    _ = (∫ s in Ioc (0 : ℝ) x,
          β * V s + K (x - s) * V s ∂volume) :=
      (integral_add (hv.const_mul β) hki).symm
    _ = (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) * V s ∂volume) := by
      apply integral_congr_ae
      filter_upwards [] with s
      ring
