-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.volumeExponentAssembly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:05:56.66224+00:00
-- url     : https://prove2.me/submissions/8c5afdad-bde3-43d0-98d7-84988435636e

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : SWArith := by
  intro k f de₀ G₀ NT v cf hk hde hdG hNT hv hcf
  have hde0 : 0 < de₀ := by linarith
  have hG0 : 0 < G₀ := by linarith
  have hNT0 : 0 < NT := by linarith
  have hde' : de₀ ≠ 0 := hde0.ne'
  have hNT' : NT ≠ 0 := hNT0.ne'
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [Real.rpow_add (div_pos hG0 hde0), Real.rpow_natCast]
  have hX0 : 0 ≤ (Real.exp 1 * Real.pi / (((j + 1 : ℕ) : ℝ) * v)) ^ ((j + 1) * f) := by positivity
  have hc : (G₀ / de₀) ^ cf ≤ G₀ ^ cf := Real.rpow_le_rpow (by positivity) (div_le_self hG0.le hde) hcf
  have hc0 : 0 ≤ (G₀ / de₀) ^ cf := by positivity
  have key : (de₀ / NT) ^ j * (G₀ / de₀) ^ (j + 1) = (G₀ / NT) ^ (j + 1) * NT / de₀ := by
    rw [div_pow, div_pow, div_pow, div_mul_div_comm, div_mul_eq_mul_div, div_div,
      div_eq_div_iff (by positivity) (by positivity)]
    ring
  have hle : (G₀ / NT) ^ (j + 1) * NT / de₀ ≤ (G₀ / NT) ^ (j + 1) * NT :=
    div_le_self (by positivity) hde
  calc _ = ((de₀ / NT) ^ j * (G₀ / de₀) ^ (j + 1)) * (G₀ / de₀) ^ cf *
        (Real.exp 1 * Real.pi / (((j + 1 : ℕ) : ℝ) * v)) ^ ((j + 1) * f) := by ring
    _ = (G₀ / NT) ^ (j + 1) * NT / de₀ * (G₀ / de₀) ^ cf *
        (Real.exp 1 * Real.pi / (((j + 1 : ℕ) : ℝ) * v)) ^ ((j + 1) * f) := by rw [key]
    _ ≤ (G₀ / NT) ^ (j + 1) * NT * G₀ ^ cf *
        (Real.exp 1 * Real.pi / (((j + 1 : ℕ) : ℝ) * v)) ^ ((j + 1) * f) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hle hc hc0 (by positivity)) hX0
    _ = _ := by ring
end Formalism.HermitianLatticeCounting.P
