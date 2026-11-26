-- Prove2me | solution 1 for FixedNumerator.det_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:43:45.856274+00:00
-- url     : https://prove2.me/submissions/497e7992-1344-4944-9777-e9a483771c45

module
public import Definitions.Def_FixedNumerator_Cases
public import Definitions.Def_FixedNumerator_Determinant
public import Theorems.Thm_FixedNumerator_one_sub_norm_le_norm_one_add

set_option autoImplicit true
@[expose] public section
public section
open Complex Real
open FixedNumerator
namespace FixedNumerator
theorem _root_.solution {N A σ : ℝ} (hN : 0 < N) {a w : ℂ} (ha : ‖a‖ ≤ N ^ A) (hw : ‖w‖ = N ^ (-σ))
    (k : ℕ) : 1 - N ^ (A - k * σ) ≤ ‖1 + a * w ^ k‖ := by
  have hwk : ‖w ^ k‖ = N ^ (-(k * σ)) := by
    rw [norm_pow, hw, ← Real.rpow_natCast, ← Real.rpow_mul hN.le]; ring_nf
  have hbound : ‖a * w ^ k‖ ≤ N ^ (A - k * σ) := by
    rw [norm_mul, hwk, sub_eq_add_neg, Real.rpow_add hN]
    exact mul_le_mul_of_nonneg_right ha (by positivity)
  linarith [one_sub_norm_le_norm_one_add (a * w ^ k)]
end FixedNumerator
