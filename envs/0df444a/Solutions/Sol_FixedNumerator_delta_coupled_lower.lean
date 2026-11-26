-- Prove2me | solution 1 for FixedNumerator.delta_coupled_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:47:38.875405+00:00
-- url     : https://prove2.me/submissions/6fda9aeb-6423-4789-b3bb-71fecd15554c

module
public import Definitions.Def_FixedNumerator_Cases
public import Definitions.Def_FixedNumerator_Determinant
public import Theorems.Thm_FixedNumerator_delta_r3_lower

set_option autoImplicit true
@[expose] public section
public section
open Complex Real
open FixedNumerator
namespace FixedNumerator
theorem _root_.solution {N σ : ℝ} (hN : 1 < N) {a₁ a₃ w : ℂ}
    (ha₁ : ‖a₁‖ ≤ N ^ ((1 : ℝ) / 2)) (ha₃ : ‖a₃‖ ≤ N ^ ((5 : ℝ) / 2)) (hw : ‖w‖ = N ^ (-σ))
    (hσ : 1 ≤ σ) :
    0 < 1 - N ^ (-1 : ℝ) ∧ 1 - N ^ (-1 : ℝ) ≤ ‖1 - a₁ * a₃ * w ^ 4‖ := by
  have hN0 : 0 < N := by linarith
  have ha : ‖-(a₁ * a₃)‖ ≤ N ^ (3 : ℝ) := by
    rw [norm_neg, norm_mul]
    calc ‖a₁‖ * ‖a₃‖ ≤ N ^ ((1 : ℝ) / 2) * N ^ ((5 : ℝ) / 2) :=
          mul_le_mul ha₁ ha₃ (norm_nonneg _) (by positivity)
      _ = N ^ (3 : ℝ) := by rw [← Real.rpow_add hN0]; norm_num
  have := delta_r3_lower hN ha hw hσ
  simpa [sub_eq_add_neg, neg_mul] using this
end FixedNumerator
