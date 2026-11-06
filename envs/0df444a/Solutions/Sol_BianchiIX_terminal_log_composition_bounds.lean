-- Prove2me | solution 1 for BianchiIX.terminal_log_composition_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T06:48:19.469016+00:00
-- url     : https://prove2.me/submissions/c039f09b-b27b-4de8-ab69-4a1375f8c23c

import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Real.Sqrt

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX


/-- The two logarithmic rows have different radial scales; only the strong row needs the
transported weak-wall amplitude to cancel its old-wall singularity. -/
theorem solution
    (M : (Fin 4 → ℝ) →L[ℝ] (Fin 2 → ℝ)) (d : Fin 4 → ℝ)
    {A B α k u v w L s t : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B)
    (hα : 0 < α ∧ α ≤ 1) (hk : 1 / α ≤ k ∧ k ≤ 3 / α)
    (hu : 0 < u ∧ u ≤ 1) (hv : 0 < v) (hw : 0 < w ∧ w ≤ 1)
    (hL : 0 ≤ L) (hs : 0 ≤ s) (ht : 0 ≤ t) (hwt : w * t ≤ B / α ^ 2)
    (hd0 : |d 0| ≤ B / α ^ 2) (hd1 : |d 1| ≤ u * (B / α))
    (hd2 : |d 2| ≤ v * (B / α + s)) (hd3 : |d 3| ≤ w * (B / α + t))
    (hUr : |M (Pi.single 0 1) 0| ≤ A * L)
    (hUu : |M (Pi.single 1 1) 0 - 1 / u| ≤ A)
    (hUv : |M (Pi.single 2 1) 0| ≤ A * k / v)
    (hUw : |M (Pi.single 3 1) 0| ≤ A)
    (hWr : |M (Pi.single 0 1) 1| ≤ A * L / k ^ 2)
    (hWu : |M (Pi.single 1 1) 1| ≤ A / k ^ 2)
    (hWv : |M (Pi.single 2 1) 1| ≤ A / v)
    (hWw : |M (Pi.single 3 1) 1 - 1 / w| ≤ A / k ^ 2) :
    |M d 0| ≤ 8 * A * B * ((1 + L) / α ^ 2 + s / α) ∧
      |M d 1| ≤ 8 * A * B * (L + 1 / α + s + t) := by
  have hA0 : 0 ≤ A := le_trans (by norm_num) hA
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB
  have hα0 : 0 < α := hα.1
  have hu0 : 0 < u := hu.1
  have hw0 : 0 < w := hw.1
  have hAB : 0 ≤ A * B := mul_nonneg hA0 hB0
  have hBA : B ≤ A * B := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hA hB0
  have hAB' : A ≤ A * B := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hB hA0
  have hα2 : 0 < α ^ 2 := sq_pos_of_pos hα.1
  have hαsq : α ^ 2 ≤ α := by nlinarith only [hα.1, hα.2]
  have hinv : 1 / α ≤ 1 / α ^ 2 := one_div_le_one_div_of_le hα2 hαsq
  have hk1 : 1 ≤ k := ((one_le_div hα.1).mpr hα.2).trans hk.1
  have hk0 : 0 < k := lt_of_lt_of_le (by norm_num) hk1
  have hk2 : 1 ≤ k ^ 2 := by nlinarith only [hk1]
  have hak : 1 ≤ α * k := by nlinarith only [(div_le_iff₀ hα.1).mp hk.1]
  have haksq : 1 ≤ α ^ 2 * k ^ 2 := by nlinarith only [sq_nonneg (α * k - 1), hak]
  have hkinv : 1 / k ^ 2 ≤ α ^ 2 := (div_le_iff₀ (sq_pos_of_pos hk0)).mpr (by linarith only [haksq])
  have hkinv1 : A / k ^ 2 ≤ A := (div_le_self hA0 hk2)
  have hlin (i : Fin 2) : |M d i| ≤ |d 0| * |M (Pi.single 0 1) i| +
      |d 1| * |M (Pi.single 1 1) i| + |d 2| * |M (Pi.single 2 1) i| +
        |d 3| * |M (Pi.single 3 1) i| := by
    have hd : d = d 0 • Pi.single 0 1 + d 1 • Pi.single 1 1 +
        d 2 • Pi.single 2 1 + d 3 • Pi.single 3 1 := by
      ext j
      fin_cases j <;> simp
    conv_lhs => rw [hd, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul]
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, abs_mul] using
      (abs_add_le (d 0 * M (Pi.single 0 1) i + d 1 * M (Pi.single 1 1) i +
        d 2 * M (Pi.single 2 1) i) (d 3 * M (Pi.single 3 1) i)).trans
          (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
  have hdiag {x a E : ℝ} (hx : 0 < x) (H : |a - 1 / x| ≤ E) : |a| ≤ 1 / x + E := by
    have H' := abs_add_le (a - 1 / x) (1 / x)
    rw [sub_add_cancel, abs_of_pos (one_div_pos.mpr hx)] at H'
    linarith only [H, H']
  have Hdu : |d 1| ≤ B / α := hd1.trans (mul_le_of_le_one_left (by positivity) hu.2)
  have Hdw : |d 3| ≤ B / α + B / α ^ 2 := hd3.trans (by
    rw [mul_add]
    exact add_le_add (mul_le_of_le_one_left (by positivity) hw.2) hwt)
  have HUr : |d 0| * |M (Pi.single 0 1) 0| ≤ A * B * L / α ^ 2 :=
    (mul_le_mul hd0 hUr (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have HUu : |d 1| * |M (Pi.single 1 1) 0| ≤ (B + A * B) / α ^ 2 := by
    have Hratio : |d 1| / u ≤ B / α := (div_le_iff₀ hu.1).mpr (by nlinarith only [hd1])
    calc
      _ ≤ |d 1| * (1 / u + A) := mul_le_mul_of_nonneg_left (hdiag hu.1 hUu) (abs_nonneg _)
      _ = |d 1| / u + A * |d 1| := by ring
      _ ≤ B / α + A * (B / α) := add_le_add Hratio (mul_le_mul_of_nonneg_left Hdu hA0)
      _ = (B + A * B) * (1 / α) := by ring
      _ ≤ (B + A * B) * (1 / α ^ 2) := mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = _ := by ring
  have HUv : |d 2| * |M (Pi.single 2 1) 0| ≤ 3 * (A * B) / α ^ 2 + 3 * A * (s / α) := by
    calc
      _ ≤ (v * (B / α + s)) * (A * k / v) := mul_le_mul hd2 hUv (abs_nonneg _) (by positivity)
      _ = A * k * (B / α + s) := by field_simp
      _ ≤ A * (3 / α) * (B / α + s) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hk.2 hA0) (by positivity)
      _ = _ := by ring
  have HUw : |d 3| * |M (Pi.single 3 1) 0| ≤ 2 * (A * B) / α ^ 2 := by
    calc
      _ ≤ (B / α + B / α ^ 2) * A := mul_le_mul Hdw hUw (abs_nonneg _) (by positivity)
      _ = A * B * (1 / α) + A * B / α ^ 2 := by ring
      _ ≤ A * B * (1 / α ^ 2) + A * B / α ^ 2 := add_le_add (mul_le_mul_of_nonneg_left hinv hAB) le_rfl
      _ = _ := by ring
  have HWr : |d 0| * |M (Pi.single 0 1) 1| ≤ A * B * L := by
    calc
      _ ≤ (B / α ^ 2) * (A * L / k ^ 2) := mul_le_mul hd0 hWr (abs_nonneg _) (by positivity)
      _ = (A * B * L / α ^ 2) * (1 / k ^ 2) := by ring
      _ ≤ (A * B * L / α ^ 2) * α ^ 2 := mul_le_mul_of_nonneg_left hkinv (by positivity)
      _ = _ := by field_simp [hα0.ne']
  have HWu : |d 1| * |M (Pi.single 1 1) 1| ≤ A * B / α :=
    (mul_le_mul Hdu (hWu.trans hkinv1) (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have HWv : |d 2| * |M (Pi.single 2 1) 1| ≤ A * B / α + A * s := by
    calc
      _ ≤ (v * (B / α + s)) * (A / v) := mul_le_mul hd2 hWv (abs_nonneg _) (by positivity)
      _ = _ := by field_simp
  have HWw : |d 3| * |M (Pi.single 3 1) 1| ≤ 2 * (A * B) / α + 2 * A * t := by
    have Hratio : |d 3| / w ≤ B / α + t := (div_le_iff₀ hw.1).mpr (by nlinarith only [hd3])
    have Hdw' : |d 3| ≤ B / α + t := hd3.trans (mul_le_of_le_one_left (by positivity) hw.2)
    have H1A : 1 + A ≤ 2 * A := by linarith only [hA]
    calc
      _ ≤ |d 3| * (1 / w + A) := mul_le_mul_of_nonneg_left (hdiag hw.1 (hWw.trans hkinv1)) (abs_nonneg _)
      _ = |d 3| / w + A * |d 3| := by ring
      _ ≤ (B / α + t) + A * (B / α + t) := add_le_add Hratio (mul_le_mul_of_nonneg_left Hdw' hA0)
      _ = (1 + A) * (B / α + t) := by ring
      _ ≤ 2 * A * (B / α + t) := mul_le_mul_of_nonneg_right H1A (by positivity)
      _ = _ := by ring
  refine ⟨?_, ?_⟩
  · have H := (hlin 0).trans (add_le_add (add_le_add (add_le_add HUr HUu) HUv) HUw)
    have HBA := div_le_div_of_nonneg_right hBA hα2.le
    have HAA := mul_le_mul_of_nonneg_right hAB' (div_nonneg hs hα.1.le)
    have HP := mul_nonneg hAB (div_nonneg hL hα2.le)
    have HQ := div_nonneg hAB hα2.le
    have HS := mul_nonneg hAB (div_nonneg hs hα.1.le)
    simp only [div_eq_mul_inv] at H HBA HAA HP HQ HS ⊢
    nlinarith only [H, HBA, HAA, HP, HQ, HS]
  · have H := (hlin 1).trans (add_le_add (add_le_add (add_le_add HWr HWu) HWv) HWw)
    have HQ := div_nonneg hAB hα.1.le
    simp only [div_eq_mul_inv] at H HQ ⊢
    nlinarith only [H, mul_le_mul_of_nonneg_right hAB' hs, mul_le_mul_of_nonneg_right hAB' ht,
      mul_nonneg hAB hL, HQ, mul_nonneg hAB hs, mul_nonneg hAB ht]
