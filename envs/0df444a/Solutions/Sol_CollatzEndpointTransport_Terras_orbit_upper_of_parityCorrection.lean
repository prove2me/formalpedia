-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.orbit_upper_of_parityCorrection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:56:37.195036+00:00
-- url     : https://prove2.me/submissions/a3dac733-bf84-428b-a59f-d90f9f36341c

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
      (oddCount k n : ℝ) ≤ (k : ℝ) / 2 + eta * k)
    (hphase :
      2 * (3 : ℝ) ^ (eta * k) ≤ (n : ℝ) ^ t)
    (hcorr :
      affineCorrection k n * (3 : ℝ) ^ ((k : ℝ) / 2) ≤
        (n : ℝ) ^ eta)
    (hcorrAbsorb :
      2 * ((n : ℝ) ^ eta * (3 : ℝ) ^ (eta * k)) ≤
        centralOrbitScale k * (n : ℝ) ^ (1 + t)) :
    ((T^[k]) n : ℝ) ≤
      centralOrbitScale k * (n : ℝ) ^ (1 + t) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hThree :
      (3 : ℝ) ^ oddCount k n ≤
        (3 : ℝ) ^ ((k : ℝ) / 2 + eta * k) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hS
  have hMain :
      (n : ℝ) / (2 : ℝ) ^ k * (3 : ℝ) ^ oddCount k n ≤
        (centralOrbitScale k * (n : ℝ) ^ (1 + t)) / 2 := by
    calc
      (n : ℝ) / (2 : ℝ) ^ k * (3 : ℝ) ^ oddCount k n
          ≤ (n : ℝ) / (2 : ℝ) ^ k *
              (3 : ℝ) ^ ((k : ℝ) / 2 + eta * k) :=
        mul_le_mul_of_nonneg_left hThree (by positivity)
      _ = centralOrbitScale k *
          ((n : ℝ) * (3 : ℝ) ^ (eta * k)) := by
        unfold centralOrbitScale
        rw [Real.rpow_add (by norm_num)]
        ring
      _ ≤ centralOrbitScale k *
          ((n : ℝ) * ((n : ℝ) ^ t / 2)) := by
        apply mul_le_mul_of_nonneg_left _ (centralOrbitScale_pos k).le
        apply mul_le_mul_of_nonneg_left _ hnR.le
        linarith
      _ = (centralOrbitScale k * (n : ℝ) ^ (1 + t)) / 2 := by
        rw [Real.rpow_add hnR, Real.rpow_one]
        ring
  have hCorr :
      affineCorrection k n * (3 : ℝ) ^ oddCount k n ≤
        (centralOrbitScale k * (n : ℝ) ^ (1 + t)) / 2 := by
    calc
      affineCorrection k n * (3 : ℝ) ^ oddCount k n
          ≤ affineCorrection k n *
              (3 : ℝ) ^ ((k : ℝ) / 2 + eta * k) :=
        mul_le_mul_of_nonneg_left hThree
          (affineCorrection_nonneg k n)
      _ = (affineCorrection k n * (3 : ℝ) ^ ((k : ℝ) / 2)) *
          (3 : ℝ) ^ (eta * k) := by
        rw [Real.rpow_add (by norm_num)]
        ring
      _ ≤ (n : ℝ) ^ eta * (3 : ℝ) ^ (eta * k) :=
        mul_le_mul_of_nonneg_right hcorr (by positivity)
      _ ≤ (centralOrbitScale k * (n : ℝ) ^ (1 + t)) / 2 := by
        linarith
  rw [iterate_eq_affineCorrection]
  calc
    ((n : ℝ) / (2 : ℝ) ^ k + affineCorrection k n) *
          (3 : ℝ) ^ oddCount k n =
        (n : ℝ) / (2 : ℝ) ^ k * (3 : ℝ) ^ oddCount k n +
          affineCorrection k n * (3 : ℝ) ^ oddCount k n := by ring
    _ ≤ (centralOrbitScale k * (n : ℝ) ^ (1 + t)) / 2 +
          (centralOrbitScale k * (n : ℝ) ^ (1 + t)) / 2 :=
      add_le_add hMain hCorr
    _ = centralOrbitScale k * (n : ℝ) ^ (1 + t) := by ring
end CollatzEndpointTransport.Terras
