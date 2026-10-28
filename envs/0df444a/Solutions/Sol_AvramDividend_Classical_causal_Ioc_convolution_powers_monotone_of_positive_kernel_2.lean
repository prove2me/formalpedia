-- Prove2me | solution 2 for AvramDividend.Classical.causal_Ioc_convolution_powers_monotone_of_positive_kernel
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:33:14.540976+00:00
-- url     : https://prove2.me/submissions/39a13c21-c372-4267-867b-877593bc77d0

import Theorems.Thm_AvramDividend_Classical_causal_Ioc_convolution_powers_full_real_recursion
import Theorems.Thm_AvramDividend_Classical_causal_continuous_product_integrable_full
import Theorems.Thm_AvramDividend_Classical_full_convolution_powers_monotone_of_nonnegative_kernel
open AvramDividend.Classical MeasureTheory Set
theorem solution
    (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ)
    (hκzero : ∀ x : ℝ, x ≤ 0 → κ x = 0)
    (hκcont : Continuous κ)
    (hκmono : Monotone κ)
    (hκpos : ∀ x : ℝ, 0 ≤ κ x)
    (hFcont : ∀ n : ℕ, Continuous (F n))
    (hF0 : F 0 = κ)
    (hFsucc : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ y in Ioc (0 : ℝ) x,
        κ y * F n (x - y) ∂volume) :
    ∀ n : ℕ, Monotone (F n) := by 
  obtain ⟨hz, hrec⟩ := causal_Ioc_convolution_powers_full_real_recursion κ F hκzero hF0 hFsucc
  refine full_convolution_powers_monotone_of_nonnegative_kernel κ F hκmono hκpos hF0 hrec ?_
  intro n x
  exact causal_continuous_product_integrable_full κ (F n) hκcont (hFcont n)
    (fun y hy => hκzero y hy.le) (fun y hy => hz n y hy.le) x
