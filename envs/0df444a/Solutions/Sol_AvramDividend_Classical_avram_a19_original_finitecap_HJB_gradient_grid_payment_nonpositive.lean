-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_original_finitecap_HJB_gradient_grid_payment_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T00:12:58.234392+00:00
-- url     : https://prove2.me/submissions/f5243f7c-6e27-4ac4-b31e-dff2395c4e43

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a19_interior_gradient_one_secant_bound
import Theorems.Thm_AvramDividend_Classical_avram_a19_caplinear_finite_grid_discounted_payment_residual_nonpositive
open Set AvramDividend.Classical

theorem solution
    {ι : Type*} (s : Finset ι) (w : ℝ → ℝ) (C : ℝ)
    (Y D E : ι → ℝ)
    (hYlo : ∀ i ∈ s, 0 ≤ Y i)
    (hYhi : ∀ i ∈ s, Y i ≤ C)
    (hD : ∀ i ∈ s, 0 ≤ D i)
    (hE : ∀ i ∈ s, 0 ≤ E i)
    (hcont : ContinuousOn w (Ici 0))
    (hdiff : ∀ i ∈ s, DifferentiableOn ℝ w (Ioo (Y i) C))
    (hgrad : ∀ i ∈ s, ∀ t ∈ Ioo (Y i) C, 1 ≤ deriv w t) :
    (∑ i ∈ s, E i * (D i + w (Y i) -
      (if Y i + D i ≤ C then w (Y i + D i)
       else w C + (Y i + D i - C)))) ≤ 0  := by
  apply avram_a19_caplinear_finite_grid_discounted_payment_residual_nonpositive
    s w C Y D E hYhi hD hE
  intro i hi z hyz hz
  have hCont : ContinuousOn w (Icc (Y i) z) :=
    hcont.mono (by
      intro t ht
      exact le_trans (hYlo i hi) ht.1)
  have hDiff : DifferentiableOn ℝ w (Ioo (Y i) z) :=
    (hdiff i hi).mono (by
      intro t ht
      exact ⟨ht.1, lt_of_lt_of_le ht.2 hz⟩)
  have hGrad : ∀ t ∈ Ioo (Y i) z, 1 ≤ deriv w t := by
    intro t ht
    exact hgrad i hi t ⟨ht.1, lt_of_lt_of_le ht.2 hz⟩
  exact avram_a19_interior_gradient_one_secant_bound
    w (Y i) z hyz hCont hDiff hGrad
