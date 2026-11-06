-- Prove2me | solution 1 for BianchiIX.compact_phase_cone_direction
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T06:51:56.257967+00:00
-- url     : https://prove2.me/submissions/69b2e6b2-1aaa-4347-b9a5-bbd051c992a1

import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX


theorem solution (J : (Fin 3 → ℝ) →L[ℝ] ℝ) (v : Fin 3 → ℝ)
    {C k x y : ℝ} (hC : 0 ≤ C) (hk : 2 ≤ k)
    (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1)
    (hv0 : v 0 = 1) (hv1 : |v 1| ≤ Real.sqrt x) (hv2 : |v 2| ≤ Real.sqrt y)
    (hJ0 : |J (Pi.single 0 1) - 1| ≤ C * (x + y ^ 2))
    (hJ12 : |J (Pi.single 1 1) + 2 / k| + |J (Pi.single 2 1)| ≤ C * (x + y)) :
    |J v - 1| ≤ (4 * C + 1) * (Real.sqrt x + y * Real.sqrt y) := by
  have hsx := Real.sqrt_nonneg x
  have hsy := Real.sqrt_nonneg y
  have hsx1 : Real.sqrt x ≤ 1 := Real.sqrt_le_one.mpr hx.2
  have hsy1 : Real.sqrt y ≤ 1 := Real.sqrt_le_one.mpr hy.2
  have hxs : x ≤ Real.sqrt x := by nlinarith only [Real.sq_sqrt hx.1, hsx, hsx1]
  have hys : y ≤ Real.sqrt y := by nlinarith only [Real.sq_sqrt hy.1, hsy, hsy1]
  have hlin : |J v - 1| ≤ |J (Pi.single 0 1) - 1| +
      |v 1| * |J (Pi.single 1 1)| + |v 2| * |J (Pi.single 2 1)| := by
    have hv : v = Pi.single 0 1 + v 1 • Pi.single 1 1 + v 2 • Pi.single 2 1 := by
      ext i
      fin_cases i <;> simp [hv0]
    have hid : J v - 1 = (J (Pi.single 0 1) - 1) + v 1 * J (Pi.single 1 1) + v 2 * J (Pi.single 2 1) := by
      conv_lhs => rw [hv, map_add, map_add, map_smul, map_smul]
      simp only [smul_eq_mul]
      ring
    rw [hid]
    simpa only [abs_mul] using (abs_add_le (J (Pi.single 0 1) - 1 + v 1 * J (Pi.single 1 1))
      (v 2 * J (Pi.single 2 1))).trans (add_le_add (abs_add_le _ _) le_rfl)
  have htwo : 0 ≤ 2 / k ∧ 2 / k ≤ 1 :=
    ⟨div_nonneg (by norm_num) (by linarith only [hk]), (div_le_one (by linarith only [hk])).mpr hk⟩
  have hJ1 : |J (Pi.single 1 1)| ≤ C * (x + y) + 1 := by
    have H := abs_sub (J (Pi.single 1 1) + 2 / k) (2 / k)
    rw [add_sub_cancel_right, abs_of_nonneg htwo.1] at H
    linarith only [H, hJ12, htwo.2, abs_nonneg (J (Pi.single 2 1))]
  have hJ2 : |J (Pi.single 2 1)| ≤ C * (x + y) := by
    linarith only [hJ12, abs_nonneg (J (Pi.single 1 1) + 2 / k)]
  have hr : |J (Pi.single 0 1) - 1| ≤ C * (Real.sqrt x + y * Real.sqrt y) := hJ0.trans
    (mul_le_mul_of_nonneg_left (by nlinarith only [hxs, mul_le_mul_of_nonneg_left hys hy.1]) hC)
  have hu : |v 1| * |J (Pi.single 1 1)| ≤ (2 * C + 1) * Real.sqrt x := by
    have H : C * (x + y) + 1 ≤ 2 * C + 1 := by nlinarith only [mul_le_mul_of_nonneg_left (add_le_add hx.2 hy.2) hC]
    have H' := mul_le_mul hv1 (hJ1.trans H) (abs_nonneg _) hsx
    simpa only [mul_comm] using H'
  have hw : |v 2| * |J (Pi.single 2 1)| ≤ C * (Real.sqrt x + y * Real.sqrt y) := by
    calc
      _ ≤ Real.sqrt y * (C * (x + y)) := mul_le_mul hv2 hJ2 (abs_nonneg _) hsy
      _ = C * (x * Real.sqrt y + y * Real.sqrt y) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (add_le_add ((mul_le_mul_of_nonneg_left hsy1 hx.1).trans (by simpa using hxs)) le_rfl) hC
  have H := hlin.trans (add_le_add (add_le_add hr hu) hw)
  have Hpos : 0 ≤ (2 * C + 1) * (y * Real.sqrt y) := by positivity [hy.1]
  nlinarith only [H, Hpos]
