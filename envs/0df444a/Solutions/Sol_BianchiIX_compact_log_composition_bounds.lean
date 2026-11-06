-- Prove2me | solution 1 for BianchiIX.compact_log_composition_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T06:48:33.923981+00:00
-- url     : https://prove2.me/submissions/d915dad8-e25d-4fd0-8315-2b8c2ee7677a

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


/-- The weak logarithmic output needs no inverse strong-wall factor. -/
theorem solution
    (J : (Fin 4 → ℝ) →L[ℝ] (Fin 2 → ℝ)) (d : Fin 4 → ℝ)
    {A B u v L ℓ s t : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hu : 0 < u) (hv : 0 < v)
    (hℓ : 0 ≤ ℓ) (hs : 0 ≤ s) (ht : 0 ≤ t) (hlog : L ≤ A + ℓ)
    (hd0 : |d 0| ≤ A) (hd1 : |d 1| ≤ A)
    (hdu : |d 1| ≤ u * (A + s)) (hdv : |d 2| ≤ v * (A + t)) (hd3 : d 3 = 0)
    (hUr : |J (Pi.single 0 1) 0| ≤ B * L)
    (hUu : |J (Pi.single 1 1) 0 - 1 / u| ≤ B)
    (hUv : |J (Pi.single 2 1) 0| ≤ 4 * B / v)
    (hWr : |J (Pi.single 0 1) 1| ≤ B * L)
    (hWu : |J (Pi.single 1 1) 1| ≤ B)
    (hWv : |J (Pi.single 2 1) 1| ≤ B / v) :
    let C := B * A ^ 2 + 6 * (B * A) + A + 4 * B + 1
    |J d 0| ≤ C * (1 + ℓ + s + t) ∧ |J d 1| ≤ C * (1 + ℓ + t) := by
  let C := B * A ^ 2 + 6 * (B * A) + A + 4 * B + 1
  have hP : 0 ≤ B * A ^ 2 := mul_nonneg hB (sq_nonneg A)
  have hQ : 0 ≤ B * A := mul_nonneg hB hA
  have hC0 : B * A ^ 2 + 5 * (B * A) + A ≤ C := by dsimp only [C]; linarith only [hQ, hB]
  have hC1 : B * A ≤ C := by dsimp only [C]; linarith only [hP, hQ, hA, hB]
  have hC2 : 1 ≤ C := by dsimp only [C]; linarith only [hP, hQ, hA, hB]
  have hC3 : 4 * B ≤ C := by dsimp only [C]; linarith only [hP, hQ, hA]
  have hC4 : B * A ^ 2 + 2 * (B * A) ≤ C := by dsimp only [C]; linarith only [hQ, hA, hB]
  have hC5 : B ≤ C := by dsimp only [C]; linarith only [hP, hQ, hA, hB]
  have hlin (i : Fin 2) : |J d i| ≤ |d 0| * |J (Pi.single 0 1) i| +
      |d 1| * |J (Pi.single 1 1) i| + |d 2| * |J (Pi.single 2 1) i| := by
    have hd : d = d 0 • Pi.single 0 1 + d 1 • Pi.single 1 1 + d 2 • Pi.single 2 1 := by
      ext j
      fin_cases j <;> simp [hd3]
    conv_lhs => rw [hd, map_add, map_add, map_smul, map_smul, map_smul]
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, abs_mul] using
      (abs_add_le (d 0 * J (Pi.single 0 1) i + d 1 * J (Pi.single 1 1) i)
        (d 2 * J (Pi.single 2 1) i)).trans (add_le_add (abs_add_le _ _) le_rfl)
  have hrad (i : Fin 2) (H : |J (Pi.single 0 1) i| ≤ B * L) :
      |d 0| * |J (Pi.single 0 1) i| ≤ B * A ^ 2 + (B * A) * ℓ := by
    calc
      _ ≤ A * (B * L) := mul_le_mul hd0 H (abs_nonneg _) hA
      _ = (B * A) * L := by ring
      _ ≤ (B * A) * (A + ℓ) := mul_le_mul_of_nonneg_left hlog hQ
      _ = _ := by ring
  have hdiag : |J (Pi.single 1 1) 0| ≤ 1 / u + B := by
    have H := abs_add_le (J (Pi.single 1 1) 0 - 1 / u) (1 / u)
    rw [sub_add_cancel, abs_of_pos (one_div_pos.mpr hu)] at H
    linarith only [H, hUu]
  have hstrong : |d 1| * |J (Pi.single 1 1) 0| ≤ A + s + B * A := by
    have hdiv : |d 1| / u ≤ A + s := (div_le_iff₀ hu).mpr (by simpa only [mul_comm] using hdu)
    calc
      _ ≤ |d 1| * (1 / u + B) := mul_le_mul_of_nonneg_left hdiag (abs_nonneg _)
      _ = |d 1| / u + B * |d 1| := by ring
      _ ≤ _ := add_le_add hdiv (mul_le_mul_of_nonneg_left hd1 hB)
  have hactive (i : Fin 2) {R : ℝ} (hR : 0 ≤ R) (H : |J (Pi.single 2 1) i| ≤ R / v) :
      |d 2| * |J (Pi.single 2 1) i| ≤ R * (A + t) := by
    calc
      _ ≤ |d 2| * (R / v) := mul_le_mul_of_nonneg_left H (abs_nonneg _)
      _ = R * (|d 2| / v) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left ((div_le_iff₀ hv).mpr (by simpa only [mul_comm] using hdv)) hR
  have hweak : |d 1| * |J (Pi.single 1 1) 1| ≤ B * A := by
    simpa only [mul_comm] using mul_le_mul hd1 hWu (abs_nonneg _) hA
  refine ⟨?_, ?_⟩
  · have H := (hlin 0).trans (add_le_add (add_le_add (hrad 0 hUr) hstrong) (hactive 0 (by positivity) hUv))
    nlinarith only [H, hC0, mul_le_mul_of_nonneg_right hC1 hℓ,
      mul_le_mul_of_nonneg_right hC2 hs, mul_le_mul_of_nonneg_right hC3 ht]
  · have H := (hlin 1).trans (add_le_add (add_le_add (hrad 1 hWr) hweak) (hactive 1 hB hWv))
    nlinarith only [H, hC4, mul_le_mul_of_nonneg_right hC1 hℓ, mul_le_mul_of_nonneg_right hC5 ht]
