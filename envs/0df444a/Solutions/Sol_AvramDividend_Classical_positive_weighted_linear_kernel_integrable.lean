-- Prove2me | solution 1 for AvramDividend.Classical.positive_weighted_linear_kernel_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T19:39:47.207137+00:00
-- url     : https://prove2.me/submissions/61eb6888-f981-4f0b-b18f-9567cf61434b

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_positive_laplace_constant_reference

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

theorem solution (K : ℝ → ℝ) (β : ℝ)
    (hK : IntegrableOn (fun t : ℝ => Real.exp (-t) * K t)
      (Ioi (0 : ℝ)) volume) :
    IntegrableOn (fun t : ℝ => Real.exp (-t) * (β + K t))
      (Ioi (0 : ℝ)) volume := by
  have he : IntegrableOn (fun t : ℝ => Real.exp (-t))
      (Ioi (0 : ℝ)) volume := by
    simpa only [one_mul] using
      (positive_laplace_constant_reference 1 (by norm_num)).1
  have hc : IntegrableOn
      (fun t : ℝ => Real.exp (-t) * β)
      (Ioi (0 : ℝ)) volume := by
    exact he.mul_const β
  have hsum := hc.add hK
  have heq :
      (fun t : ℝ => Real.exp (-t) * (β + K t)) =
      (fun t : ℝ => Real.exp (-t) * β +
        Real.exp (-t) * K t) := by
    funext t
    ring
  rw [heq]
  exact hsum
