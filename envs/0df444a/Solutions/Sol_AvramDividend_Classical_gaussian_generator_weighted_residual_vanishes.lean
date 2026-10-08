-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_generator_weighted_residual_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:34:41.001289+00:00
-- url     : https://prove2.me/submissions/aa70318e-9cff-4bcf-8d84-f18d1a847d2c

import Mathlib
import Theorems.Thm_AvramDividend_Classical_gaussian_generator_laplace_cancellation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    (fD fJ fW : ℝ → ℝ) (d c θ q ψ J η : ℝ)
    (hD : IntegrableOn fD (Ioi (0 : ℝ)))
    (hJ : IntegrableOn fJ (Ioi (0 : ℝ)))
    (hW : IntegrableOn fW (Ioi (0 : ℝ)))
    (hDtr : (∫ x in Ioi (0 : ℝ), fD x) =
      (d * θ ^ 2 + c * θ) * (ψ - q)⁻¹ - d * η)
    (hJtr : (∫ x in Ioi (0 : ℝ), fJ x) =
      J * (ψ - q)⁻¹)
    (hWtr : (∫ x in Ioi (0 : ℝ), fW x) = (ψ - q)⁻¹)
    (hψ : ψ = d * θ ^ 2 + c * θ + J)
    (hqψ : q < ψ) (horigin : d * η = 1) :
    (∫ x in Ioi (0 : ℝ), (fD x + fJ x - q * fW x)) = 0 := by
  have hQ : IntegrableOn (fun x : ℝ => q * fW x) (Ioi (0 : ℝ)) :=
    hW.const_mul q
  calc
    (∫ x in Ioi (0 : ℝ), fD x + fJ x - q * fW x) =
      (∫ x in Ioi (0 : ℝ), fD x) +
      (∫ x in Ioi (0 : ℝ), fJ x) -
      q * (∫ x in Ioi (0 : ℝ), fW x) := by
        have hSub :
            (∫ x in Ioi (0 : ℝ), fD x + fJ x - q * fW x) =
              (∫ x in Ioi (0 : ℝ), fD x + fJ x) -
                (∫ x in Ioi (0 : ℝ), q * fW x) :=
          integral_sub (hD.add hJ) hQ
        rw [hSub, integral_add hD hJ, integral_const_mul]
    _ = (d * θ ^ 2 + c * θ + J - q) * (ψ - q)⁻¹ - d * η := by
      rw [hDtr, hJtr, hWtr]
      ring
    _ = 0 := gaussian_generator_laplace_cancellation
      d c θ q ψ J η hψ hqψ horigin
