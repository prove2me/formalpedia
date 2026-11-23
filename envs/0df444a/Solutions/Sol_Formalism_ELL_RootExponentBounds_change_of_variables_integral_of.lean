-- Prove2me | solution 1 for Formalism.ELL.RootExponentBounds.change_of_variables_integral_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:26:29.993518+00:00
-- url     : https://prove2.me/submissions/ab733bfb-83e6-4235-9b49-fc2a505a23d1

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_ChangeIntegral
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_Change
import Theorems.Thm_Formalism_ELL_RootExponentBounds_root2
import Theorems.Thm_Formalism_ELL_RootExponentBounds_root3
import Theorems.Thm_Formalism_ELL_RootExponentBounds_root4
import Theorems.Thm_Formalism_ELL_RootExponentBounds_bmem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.ELL Formalism.G
open Formalism Formalism.ELL Formalism.ELL.RootExponentBounds
universe u
namespace Formalism.ELL.RootExponentBounds
theorem _root_.solution : ChangeIntegral.{u} := by
  intro K _ _ W C hW hW' hΔ0 hΔ
  set W' := C • W with hW'def
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  obtain ⟨h1', h2', h3', h4', h6'⟩ := hW'

  have hv : ‖((C.u⁻¹ : Kˣ) : K)‖ = 1 := by
    have e := WeierstrassCurve.variableChange_Δ W C
    rw [← hW'def] at e
    rw [e, norm_mul, norm_pow] at hΔ
    have hn : ‖W.Δ‖ ≠ 0 := norm_ne_zero_iff.2 hΔ0
    have : ‖((C.u⁻¹ : Kˣ) : K)‖ ^ 12 = 1 := by
      have := mul_right_cancel₀ hn (hΔ.trans (one_mul _).symm); exact this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 this
  have hu : ‖(C.u : K)‖ = 1 := by
    rw [Units.val_inv_eq_inv_val, norm_inv, inv_eq_one] at hv; exact hv
  set u : K := (C.u : K)
  set v : K := ((C.u⁻¹ : Kˣ) : K)
  have hvu : v * u = 1 := by simp [u, v]
  have hvu2 : v ^ 2 * u ^ 2 = 1 := by rw [← mul_pow, hvu, one_pow]
  have hvu6 : v ^ 6 * u ^ 6 = 1 := by rw [← mul_pow, hvu, one_pow]
  have hvu8 : v ^ 8 * u ^ 8 = 1 := by rw [← mul_pow, hvu, one_pow]
  rw [← memB] at h1 h2 h3 h4 h6 h1' h2' h3' h4' h6'
  have hu' : u ∈ unitBall K := by rw [memB, hu]
  obtain ⟨hb2, hb4, hb6, hb8⟩ := bmem W h1 h2 h3 h4 h6
  obtain ⟨-, -, hb6', hb8'⟩ := bmem W' h1' h2' h3' h4' h6'

  have hr : C.r ∈ unitBall K := by
    rw [memB]
    rcases (IsUltrametricDist.norm_natCast_le_one K 2).lt_or_eq with h2lt | h2eq
    ·
      have h3n : ‖(3 : K)‖ = 1 := by
        have h3le : ‖(3 : K)‖ ≤ 1 := by exact_mod_cast IsUltrametricDist.norm_natCast_le_one K 3
        have : ‖(1 : K)‖ ≤ max ‖(3 : K)‖ ‖(2 : K)‖ := by
          have := IsUltrametricDist.norm_add_le_max (3 : K) (-2)
          rw [norm_neg] at this
          have e : (3 : K) + -2 = 1 := by norm_num
          rwa [e] at this
        rw [norm_one] at this
        push_cast at h2lt
        rcases le_max_iff.1 this with h | h
        · exact le_antisymm h3le h
        · linarith
      have e8 := WeierstrassCurve.variableChange_b₈ W C
      rw [← hW'def] at e8
      have key : (3 : K) * C.r ^ 4 + W.b₂ * C.r ^ 3 + (3 * W.b₄) * C.r ^ 2 + (3 * W.b₆) * C.r
          + (W.b₈ - u ^ 8 * W'.b₈) = 0 := by
        linear_combination (-u ^ 8) * e8 - (W.b₈ + 3 * C.r * W.b₆ + 3 * C.r ^ 2 * W.b₄
          + C.r ^ 3 * W.b₂ + 3 * C.r ^ 4) * hvu8
      refine root4 h3n (memB.1 hb2) (memB.1 (by (repeat (first
  | assumption | apply ofNatB
  | apply add_mem | apply sub_mem | apply mul_mem | apply pow_mem | apply neg_mem)))) (memB.1 (by (repeat (first
  | assumption | apply ofNatB
  | apply add_mem | apply sub_mem | apply mul_mem | apply pow_mem | apply neg_mem)))) (memB.1 (by (repeat (first
  | assumption | apply ofNatB
  | apply add_mem | apply sub_mem | apply mul_mem | apply pow_mem | apply neg_mem)))) key
    ·
      have h4n : ‖(4 : K)‖ = 1 := by
        have : (4 : K) = 2 * 2 := by norm_num
        rw [this, norm_mul]; push_cast at h2eq; rw [h2eq]; norm_num
      have e6 := WeierstrassCurve.variableChange_b₆ W C
      rw [← hW'def] at e6
      have key : (4 : K) * C.r ^ 3 + W.b₂ * C.r ^ 2 + (2 * W.b₄) * C.r
          + (W.b₆ - u ^ 6 * W'.b₆) = 0 := by
        linear_combination (-u ^ 6) * e6 - (W.b₆ + 2 * C.r * W.b₄ + C.r ^ 2 * W.b₂
          + 4 * C.r ^ 3) * hvu6
      exact root3 h4n (memB.1 hb2) (memB.1 (by (repeat (first
  | assumption | apply ofNatB
  | apply add_mem | apply sub_mem | apply mul_mem | apply pow_mem | apply neg_mem)))) (memB.1 (by (repeat (first
  | assumption | apply ofNatB
  | apply add_mem | apply sub_mem | apply mul_mem | apply pow_mem | apply neg_mem)))) key

  have hs : C.s ∈ unitBall K := by
    have e2 : W'.a₂ = v ^ 2 * (W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2) := rfl
    have key : C.s ^ 2 + W.a₁ * C.s + (-W.a₂ - 3 * C.r + u ^ 2 * W'.a₂) = 0 := by
      linear_combination u ^ 2 * e2 + (W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2) * hvu2
    exact memB.2 (root2 (memB.1 h1) (memB.1 (by (repeat (first
  | assumption | apply ofNatB
  | apply add_mem | apply sub_mem | apply mul_mem | apply pow_mem | apply neg_mem)))) key)

  have ht : C.t ∈ unitBall K := by
    have e6 : W'.a₆ = v ^ 6 * (W.a₆ + C.r * W.a₄ + C.r ^ 2 * W.a₂ + C.r ^ 3 - C.t * W.a₃
        - C.t ^ 2 - C.r * C.t * W.a₁) := rfl
    have key : C.t ^ 2 + (W.a₃ + C.r * W.a₁) * C.t
        + (-(W.a₆ + C.r * W.a₄ + C.r ^ 2 * W.a₂ + C.r ^ 3) + u ^ 6 * W'.a₆) = 0 := by
      linear_combination u ^ 6 * e6 + (W.a₆ + C.r * W.a₄ + C.r ^ 2 * W.a₂ + C.r ^ 3 - C.t * W.a₃
        - C.t ^ 2 - C.r * C.t * W.a₁) * hvu6
    exact memB.2 (root2 (memB.1 (by (repeat (first
  | assumption | apply ofNatB
  | apply add_mem | apply sub_mem | apply mul_mem | apply pow_mem | apply neg_mem)))) (memB.1 (by (repeat (first
  | assumption | apply ofNatB
  | apply add_mem | apply sub_mem | apply mul_mem | apply pow_mem | apply neg_mem)))) key)
  exact ⟨hu, memB.1 hr, memB.1 hs, memB.1 ht⟩
end Formalism.ELL.RootExponentBounds
