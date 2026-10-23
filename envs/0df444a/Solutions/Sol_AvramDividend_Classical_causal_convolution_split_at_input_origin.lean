-- Prove2me | solution 1 for AvramDividend.Classical.causal_convolution_split_at_input_origin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T22:57:08.099564+00:00
-- url     : https://prove2.me/submissions/01528e62-cb55-4312-bc81-d92b45103de2

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_causal_l1_kernel_continuous_input_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (K f : ℝ → ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hf : ContinuousOn f (Ici (0 : ℝ)))
    (x : ℝ) (hx : 0 < x) :
    (∫ s in Ioc (0 : ℝ) x, K (x - s) * f s ∂volume) =
      f 0 * (∫ s in Ioc (0 : ℝ) x, K (x - s) ∂volume) +
      (∫ s in Ioc (0 : ℝ) x,
        K (x - s) * (f s - f 0) ∂volume) := by
  have hker : IntegrableOn (fun s : ℝ => K (x - s))
      (Ioc (0 : ℝ) x) volume := by
    have hunit := causal_l1_kernel_continuous_input_integrable
      K (fun _ : ℝ => (1 : ℝ)) hK continuousOn_const x hx
    simpa only [mul_one] using hunit
  have hconst : IntegrableOn (fun s : ℝ => f 0 * K (x - s))
      (Ioc (0 : ℝ) x) volume := hker.const_mul (f 0)
  have hdev : ContinuousOn (fun s : ℝ => f s - f 0)
      (Ici (0 : ℝ)) := hf.sub continuousOn_const
  have hintdev := causal_l1_kernel_continuous_input_integrable
    K (fun s : ℝ => f s - f 0) hK hdev x hx
  calc
    (∫ s in Ioc (0 : ℝ) x, K (x - s) * f s ∂volume) =
      (∫ s in Ioc (0 : ℝ) x,
        f 0 * K (x - s) + K (x - s) * (f s - f 0) ∂volume) := by
      apply integral_congr_ae
      filter_upwards [] with s
      ring
    _ = (∫ s in Ioc (0 : ℝ) x, f 0 * K (x - s) ∂volume) +
        (∫ s in Ioc (0 : ℝ) x, K (x - s) * (f s - f 0) ∂volume) :=
          integral_add hconst hintdev
    _ = _ := by rw [integral_const_mul]
