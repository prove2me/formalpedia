-- Prove2me | solution 1 for FixedNumerator.det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:45:44.375901+00:00
-- url     : https://prove2.me/submissions/77da67c9-a8d4-422a-bafb-b1ea7bd1a2eb

module
public import Definitions.Def_FixedNumerator_Cases
public import Definitions.Def_FixedNumerator_Determinant
public import Theorems.Thm_FixedNumerator_det_lower

set_option autoImplicit true
@[expose] public section
public section
open Complex Real
open FixedNumerator
namespace FixedNumerator
theorem _root_.solution {N A σ : ℝ} (hN : 1 < N) {a w : ℂ} (ha : ‖a‖ ≤ N ^ A)
    (hw : ‖w‖ = N ^ (-σ)) (k : ℕ) (h : A < k * σ) : 1 + a * w ^ k ≠ 0 := by
  intro h0
  have := det_lower (by linarith) ha hw k
  rw [h0, norm_zero] at this
  have : N ^ (A - k * σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hN (by linarith)
  linarith
end FixedNumerator
