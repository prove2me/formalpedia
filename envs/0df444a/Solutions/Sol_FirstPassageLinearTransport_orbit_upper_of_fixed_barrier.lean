-- Prove2me | solution 1 for FirstPassageLinearTransport.orbit_upper_of_fixed_barrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:24:58.26366+00:00
-- url     : https://prove2.me/submissions/e2a22189-0052-4566-bc3d-84bbf969fd28

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
theorem _root_.solution {n k : ℕ} {h t C : ℝ}
    (hn : 0 < n)
    (hS : (oddCount n k : ℝ) ≤ (k : ℝ) / 2 + h)
    (hphase : 2 * (3 : ℝ) ^ h ≤ (n : ℝ) ^ t)
    (hcorr : normalizedCorrection k n * (3 : ℝ) ^ ((k : ℝ) / 2) ≤
      C * (3 : ℝ) ^ h)
    (hcorrAbsorb :
      2 * (C * (3 : ℝ) ^ h * (3 : ℝ) ^ h) ≤
        centralOrbitScale k * (n : ℝ) ^ (1 + t)) :
    (orbit k n : ℝ) ≤ centralOrbitScale k * (n : ℝ) ^ (1 + t) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hThree :
      (3 : ℝ) ^ oddCount n k ≤ (3 : ℝ) ^ ((k : ℝ) / 2 + h) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hS
  have hMain :
      (n : ℝ) / (2 : ℝ) ^ k * (3 : ℝ) ^ oddCount n k ≤
        (centralOrbitScale k * (n : ℝ) ^ (1 + t)) / 2 := by
    calc
      _ ≤ (n : ℝ) / (2 : ℝ) ^ k * (3 : ℝ) ^ ((k : ℝ) / 2 + h) :=
        mul_le_mul_of_nonneg_left hThree (by positivity)
      _ = centralOrbitScale k * ((n : ℝ) * (3 : ℝ) ^ h) := by
        unfold centralOrbitScale
        rw [Real.rpow_add (by norm_num)]
        ring
      _ ≤ centralOrbitScale k * ((n : ℝ) * ((n : ℝ) ^ t / 2)) := by
        apply mul_le_mul_of_nonneg_left _ (centralOrbitScale_pos k).le
        apply mul_le_mul_of_nonneg_left _ hnR.le
        linarith
      _ = (centralOrbitScale k * (n : ℝ) ^ (1 + t)) / 2 := by
        rw [Real.rpow_add hnR, Real.rpow_one]
        ring
  have hCorr :
      normalizedCorrection k n * (3 : ℝ) ^ oddCount n k ≤
        (centralOrbitScale k * (n : ℝ) ^ (1 + t)) / 2 := by
    calc
      _ ≤ normalizedCorrection k n * (3 : ℝ) ^ ((k : ℝ) / 2 + h) :=
        mul_le_mul_of_nonneg_left hThree
          (normalizedCorrection_nonneg k n)
      _ = (normalizedCorrection k n * (3 : ℝ) ^ ((k : ℝ) / 2)) *
          (3 : ℝ) ^ h := by
        rw [Real.rpow_add (by norm_num)]
        ring
      _ ≤ (C * (3 : ℝ) ^ h) * (3 : ℝ) ^ h :=
        mul_le_mul_of_nonneg_right hcorr (by positivity)
      _ ≤ (centralOrbitScale k * (n : ℝ) ^ (1 + t)) / 2 := by
        linarith
  rw [orbit_eq_normalizedCorrection]
  calc
    _ = (n : ℝ) / (2 : ℝ) ^ k * (3 : ℝ) ^ oddCount n k +
        normalizedCorrection k n * (3 : ℝ) ^ oddCount n k := by ring
    _ ≤ (centralOrbitScale k * (n : ℝ) ^ (1 + t)) / 2 +
        (centralOrbitScale k * (n : ℝ) ^ (1 + t)) / 2 :=
      add_le_add hMain hCorr
    _ = _ := by ring
end FirstPassageLinearTransport
