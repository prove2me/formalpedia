-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsSubgroup.y_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:20.066083+00:00
-- url     : https://prove2.me/submissions/97a478c1-bf86-40a7-8171-6069968a3f3b

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
theorem _root_.solution (W : WeierstrassCurve K)
    (hW : IntegralModel W) {x y : K} (h : W.toAffine.Equation x y) (hx : ‖x‖ ≤ 1) : ‖y‖ ≤ 1 := by
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  have h' : y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ :=
    (WeierstrassCurve.Affine.equation_iff _ _).mp h
  by_contra hy
  push_neg at hy
  have hR : ‖x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆‖ ≤ 1 := by
    have hx2 : ‖x ^ 2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx
    have hx3 : ‖x ^ 3‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx
    refine add_le (add_le (add_le hx3 ?_) ?_) h6
    · simpa using mul_le h2 hx2
    · simpa using mul_le h4 hx
  have hT : ‖W.a₁ * x * y + W.a₃ * y‖ ≤ ‖y‖ := by
    refine add_le ?_ ?_
    · simpa using mul_le (mul_le h1 hx) (le_refl ‖y‖)
    · simpa using mul_le h3 (le_refl ‖y‖)
  have hlt : ‖-(W.a₁ * x * y + W.a₃ * y)‖ < ‖y ^ 2‖ := by
    rw [norm_neg, norm_pow]; nlinarith
  have key := le_sub_of_lt hlt
  rw [sub_neg_eq_add, ← add_assoc, h', norm_pow] at key
  nlinarith
end Formalism.ELL.FormalGroupPointsSubgroup
