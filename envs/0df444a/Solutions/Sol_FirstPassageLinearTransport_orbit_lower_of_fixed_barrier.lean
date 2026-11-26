-- Prove2me | solution 1 for FirstPassageLinearTransport.orbit_lower_of_fixed_barrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:24:52.127302+00:00
-- url     : https://prove2.me/submissions/30d3e23f-c98a-47eb-8d5b-0b7f0fcb173d

import Mathlib.Algebra.Ring.GeomSum
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_Envelope
import Theorems.Thm_FirstPassageLinearTransport_centralOrbitScale_pos
import Theorems.Thm_FirstPassageLinearTransport_normalizedCorrection_nonneg
import Theorems.Thm_FirstPassageLinearTransport_orbit_eq_normalizedCorrection

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution {n k : ℕ} {h t : ℝ}
    (hn : 0 < n)
    (hS : (k : ℝ) / 2 - h ≤ (oddCount n k : ℝ))
    (hphase : (3 : ℝ) ^ h ≤ (n : ℝ) ^ t) :
    centralOrbitScale k * (n : ℝ) ^ (1 - t) ≤ (orbit k n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hInv : (n : ℝ) / (n : ℝ) ^ t ≤ (n : ℝ) / (3 : ℝ) ^ h :=
    div_le_div_of_nonneg_left hnR.le (by positivity) hphase
  have hThree :
      (3 : ℝ) ^ ((k : ℝ) / 2 - h) ≤ (3 : ℝ) ^ oddCount n k := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hS
  rw [orbit_eq_normalizedCorrection]
  calc
    centralOrbitScale k * (n : ℝ) ^ (1 - t) =
        centralOrbitScale k * ((n : ℝ) / (n : ℝ) ^ t) := by
      rw [Real.rpow_sub hnR, Real.rpow_one]
    _ ≤ centralOrbitScale k * ((n : ℝ) / (3 : ℝ) ^ h) :=
      mul_le_mul_of_nonneg_left hInv (centralOrbitScale_pos k).le
    _ = (n : ℝ) / (2 : ℝ) ^ k *
        (3 : ℝ) ^ ((k : ℝ) / 2 - h) := by
      unfold centralOrbitScale
      rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 3)]
      ring
    _ ≤ (n : ℝ) / (2 : ℝ) ^ k * (3 : ℝ) ^ oddCount n k :=
      mul_le_mul_of_nonneg_left hThree (by positivity)
    _ ≤ ((n : ℝ) / (2 : ℝ) ^ k + normalizedCorrection k n) *
        (3 : ℝ) ^ oddCount n k :=
      mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right (normalizedCorrection_nonneg k n))
        (by positivity)
end FirstPassageLinearTransport
