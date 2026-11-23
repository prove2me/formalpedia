-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsSubgroup.y_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:20.281285+00:00
-- url     : https://prove2.me/submissions/aa662db8-633c-4fc7-88d2-2a53b7f47398

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsTorsionFree
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsSubgroupHolds
import Theorems.Thm_Formalism_ELL_FormalGroupPointsSubgroup_add_le
import Theorems.Thm_Formalism_ELL_FormalGroupPointsSubgroup_le_sub_of_lt
import Theorems.Thm_Formalism_ELL_FormalGroupPointsSubgroup_mul_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open Formalism Formalism.ELL Formalism.ELL.FormalGroupPointsSubgroup
open WeierstrassCurve Polynomial
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.ELL.FormalGroupPointsSubgroup
theorem _root_.solution (W : WeierstrassCurve K) (hW : IntegralModel W) {x y : K}
    (h : W.toAffine.Equation x y) (hx : 1 < ‖x‖) : ‖y‖ ^ 2 ≤ ‖x‖ ^ 3 := by
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  have h' : y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ :=
    (WeierstrassCurve.Affine.equation_iff _ _).mp h
  by_contra hy
  push_neg at hy
  have hx0 : (0 : ℝ) < ‖x‖ := by linarith
  have hx2 : ‖x‖ ^ 2 < ‖x‖ ^ 3 := by
    nlinarith [mul_pos (mul_pos hx0 hx0) (by linarith : (0 : ℝ) < ‖x‖ - 1)]
  have hx1 : ‖x‖ ≤ ‖x‖ ^ 3 := by
    nlinarith [mul_pos hx0 (by linarith : (0 : ℝ) < ‖x‖ - 1)]
  have hxy : ‖x‖ < ‖y‖ := by
    by_contra hc
    push_neg at hc
    have := mul_le_mul hc hc (norm_nonneg y) hx0.le
    nlinarith
  have hR : ‖x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆‖ ≤ ‖x‖ ^ 3 := by
    refine add_le (add_le (add_le (le_of_eq (norm_pow _ _)) ?_) ?_) ?_
    · exact (mul_le h2 (le_of_eq (norm_pow x 2))).trans (by linarith)
    · exact (mul_le h4 (le_refl ‖x‖)).trans (by linarith)
    · exact h6.trans (one_le_pow₀ hx.le)
  have hT : ‖W.a₁ * x * y + W.a₃ * y‖ ≤ ‖x‖ * ‖y‖ := by
    refine add_le ?_ ?_
    · simpa using mul_le (mul_le h1 (le_refl ‖x‖)) (le_refl ‖y‖)
    · exact (mul_le h3 (le_refl ‖y‖)).trans (by nlinarith [norm_nonneg y])
  have hlt : ‖-(W.a₁ * x * y + W.a₃ * y)‖ < ‖y ^ 2‖ := by
    rw [norm_neg, norm_pow]; nlinarith [norm_nonneg y]
  have key := le_sub_of_lt hlt
  rw [sub_neg_eq_add, ← add_assoc, h', norm_pow] at key
  linarith
end Formalism.ELL.FormalGroupPointsSubgroup
