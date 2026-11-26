-- Prove2me | solution 1 for FixedNumerator.delta_r3_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:45:42.631801+00:00
-- url     : https://prove2.me/submissions/288801ec-0c71-495f-8d79-e4ea7a9f0d76

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
theorem _root_.solution {N σ : ℝ} (hN : 1 < N) {a w : ℂ} (ha : ‖a‖ ≤ N ^ (3 : ℝ))
    (hw : ‖w‖ = N ^ (-σ)) (hσ : 1 ≤ σ) :
    0 < 1 - N ^ (-1 : ℝ) ∧ 1 - N ^ (-1 : ℝ) ≤ ‖1 + a * w ^ 4‖ := by
  constructor
  · have := Real.rpow_lt_one_of_one_lt_of_neg hN (show (-1 : ℝ) < 0 by norm_num)
    linarith
  · have h := det_lower (by linarith) ha hw 4
    have : N ^ ((3 : ℝ) - (4 : ℕ) * σ) ≤ N ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hN.le (by push_cast; linarith)
    linarith
end FixedNumerator
