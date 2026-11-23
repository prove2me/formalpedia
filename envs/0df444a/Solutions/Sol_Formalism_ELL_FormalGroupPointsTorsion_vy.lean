-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsTorsion.vy
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:09:44.513799+00:00
-- url     : https://prove2.me/submissions/f8e84661-3485-4852-8750-81c52cbdf5c6

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsTorsionFree
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsNoPrimeToPTorsion
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_add_le
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_dom
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_mul_le_of_one

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
open Formalism Formalism.ELL Formalism.ELL.FormalGroupPointsTorsion
open WeierstrassCurve Polynomial
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
variable {W : WeierstrassCurve K}
namespace Formalism.ELL.FormalGroupPointsTorsion
theorem _root_.solution (hW : IntegralModel W) {x y : K} (h : W.toAffine.Equation x y) (hx : 1 < ‖x‖) :
    ‖y‖ ^ 2 = ‖x‖ ^ 3 ∧ ‖x‖ < ‖y‖ := by
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  rw [Affine.equation_iff] at h
  have key : y ^ 2 + (W.a₁ * x + W.a₃) * y = x ^ 3 + (W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) := by
    linear_combination h
  have hX0 : 0 ≤ ‖x‖ := norm_nonneg _
  have hc : ‖W.a₁ * x + W.a₃‖ ≤ ‖x‖ := add_le (mul_le_of_one h1) (h3.trans hx.le)
  have hXX : ‖x‖ ≤ ‖x‖ ^ 2 := by nlinarith
  have hr : ‖W.a₂ * x ^ 2 + W.a₄ * x + W.a₆‖ ≤ ‖x‖ ^ 2 := by
    refine add_le (add_le ?_ ?_) ?_
    · exact (mul_le_of_one h2).trans (by rw [norm_pow])
    · exact (mul_le_of_one h4).trans hXX
    · nlinarith
  have hR : ‖x ^ 3 + (W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)‖ = ‖x‖ ^ 3 := by
    have : ‖W.a₂ * x ^ 2 + W.a₄ * x + W.a₆‖ < ‖x ^ 3‖ := by
      rw [norm_pow]; nlinarith
    rw [dom this, norm_pow]
  have hyx : ‖x‖ < ‖y‖ := by
    by_contra hle
    push_neg at hle
    have : ‖y ^ 2 + (W.a₁ * x + W.a₃) * y‖ ≤ ‖x‖ ^ 2 := by
      refine add_le ?_ ?_
      · rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hle 2
      · rw [norm_mul, sq]; exact mul_le_mul hc hle (norm_nonneg _) hX0
    rw [key, hR] at this
    nlinarith
  refine ⟨?_, hyx⟩
  have hlt : ‖(W.a₁ * x + W.a₃) * y‖ < ‖y ^ 2‖ := by
    rw [norm_mul, norm_pow, sq]
    exact mul_lt_mul_of_pos_right (hc.trans_lt hyx) (by linarith)
  have : ‖y ^ 2 + (W.a₁ * x + W.a₃) * y‖ = ‖y‖ ^ 2 := by rw [dom hlt, norm_pow]
  rw [← this, key, hR]
end Formalism.ELL.FormalGroupPointsTorsion
