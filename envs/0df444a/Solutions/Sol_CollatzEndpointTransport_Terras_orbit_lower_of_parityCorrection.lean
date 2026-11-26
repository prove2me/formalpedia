-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.orbit_lower_of_parityCorrection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:56:29.771859+00:00
-- url     : https://prove2.me/submissions/47b2edf5-3535-4291-bfa8-47fead199f46

import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
import Definitions.Def_CollatzEndpointTransport_Common_TerrasAffineIterate
import Definitions.Def_CollatzEndpointTransport_Common_TerrasOrbitEnvelope
import Theorems.Thm_CollatzEndpointTransport_Terras_centralOrbitScale_pos
import Theorems.Thm_CollatzEndpointTransport_Terras_affineCorrection_nonneg
import Theorems.Thm_CollatzEndpointTransport_Terras_iterate_eq_affineCorrection


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset
open scoped Real
namespace CollatzEndpointTransport.Terras
theorem _root_.solution
    {n k : ℕ} {eta t : ℝ}
    (hn : 0 < n)
    (hS :
      (k : ℝ) / 2 - eta * k ≤ (oddCount k n : ℝ))
    (hphase :
      (3 : ℝ) ^ (eta * k) ≤ (n : ℝ) ^ t) :
    centralOrbitScale k * (n : ℝ) ^ (1 - t) ≤
      ((T^[k]) n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h3eta : 0 < (3 : ℝ) ^ (eta * k) := by positivity
  have hInv :
      (n : ℝ) / (n : ℝ) ^ t ≤
        (n : ℝ) / (3 : ℝ) ^ (eta * k) :=
    div_le_div_of_nonneg_left hnR.le h3eta hphase
  have hScale : 0 ≤ centralOrbitScale k :=
    (centralOrbitScale_pos k).le
  have hTarget :
      centralOrbitScale k * (n : ℝ) ^ (1 - t) ≤
        (n : ℝ) / (2 : ℝ) ^ k *
          (3 : ℝ) ^ ((k : ℝ) / 2 - eta * k) := by
    rw [Real.rpow_sub hnR, Real.rpow_one]
    calc
      centralOrbitScale k * ((n : ℝ) / (n : ℝ) ^ t)
          ≤ centralOrbitScale k *
              ((n : ℝ) / (3 : ℝ) ^ (eta * k)) :=
        mul_le_mul_of_nonneg_left hInv hScale
      _ = (n : ℝ) / (2 : ℝ) ^ k *
          (3 : ℝ) ^ ((k : ℝ) / 2 - eta * k) := by
        unfold centralOrbitScale
        rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 3)]
        ring
  have hThree :
      (3 : ℝ) ^ ((k : ℝ) / 2 - eta * k) ≤
        (3 : ℝ) ^ oddCount k n := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hS
  rw [iterate_eq_affineCorrection]
  calc
    centralOrbitScale k * (n : ℝ) ^ (1 - t)
        ≤ (n : ℝ) / (2 : ℝ) ^ k *
            (3 : ℝ) ^ ((k : ℝ) / 2 - eta * k) := hTarget
    _ ≤ (n : ℝ) / (2 : ℝ) ^ k *
          (3 : ℝ) ^ oddCount k n :=
      mul_le_mul_of_nonneg_left hThree (by positivity)
    _ ≤ ((n : ℝ) / (2 : ℝ) ^ k + affineCorrection k n) *
          (3 : ℝ) ^ oddCount k n := by
      exact mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right (affineCorrection_nonneg k n))
        (by positivity)
end CollatzEndpointTransport.Terras
