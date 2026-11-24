-- Prove2me | solution 1 for DeletedPrimes.meanSq_le_of_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:03:53.676789+00:00
-- url     : https://prove2.me/submissions/5fe86b79-df36-4fe3-8379-82ab7f5fe2d6

import Mathlib
import Definitions.Def_DeletedPrimes_Basic
import Theorems.Thm_DeletedPrimes_intervalIntegrable_err_sq

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
open Classical
namespace DeletedPrimes
theorem _root_.solution {S : Set ℕ} {X M : ℝ} (hX : 1 ≤ X)
    (h : ∀ x ∈ Set.Icc X (2 * X), err S x ^ 2 ≤ M) : meanSq S X ≤ M := by
  unfold meanSq
  have hX0 : 0 < X := by linarith
  have hle : X ≤ 2 * X := by linarith
  have hint : ∫ x in X..2 * X, err S x ^ 2 ≤ ∫ _x in X..2 * X, M :=
    intervalIntegral.integral_mono_on hle (intervalIntegrable_err_sq S hX0.le hle)
      intervalIntegrable_const h
  rw [intervalIntegral.integral_const, smul_eq_mul] at hint
  have : X⁻¹ * ∫ x in X..2 * X, err S x ^ 2 ≤ X⁻¹ * ((2 * X - X) * M) :=
    mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr hX0.le)
  calc X⁻¹ * ∫ x in X..2 * X, err S x ^ 2 ≤ X⁻¹ * ((2 * X - X) * M) := this
    _ = M := by field_simp; ring
end DeletedPrimes
