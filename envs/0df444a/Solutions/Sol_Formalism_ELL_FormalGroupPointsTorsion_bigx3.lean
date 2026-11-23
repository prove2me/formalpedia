-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsTorsion.bigx3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:23:11.485297+00:00
-- url     : https://prove2.me/submissions/3dfcee68-63a8-4cad-b36a-acf182ed896e

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsTorsionFree
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsNoPrimeToPTorsion
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_add_le
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_sub_le
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_dom
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_mul_le_of_one
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_two_le
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_lsq
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_realC

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
theorem _root_.solution (hW : IntegralModel W) {x1 x2 x3 y3 l v : K} (hX1 : 1 < ‖x1‖) (hX2 : 1 < ‖x2‖)
    (h3 : W.toAffine.Equation x3 y3) (hy3 : y3 = l * x3 + v)
    (e1 : l ^ 2 + W.a₁ * l - W.a₂ = x1 + x2 + x3)
    (e2 : W.a₄ - 2 * l * v - W.a₁ * v - W.a₃ * l = x1 * x2 + x3 * (x1 + x2)) : 1 < ‖x3‖ := by
  by_contra hx3
  push_neg at hx3
  obtain ⟨h1, h2, h3', h4, h6⟩ := hW
  have hy3n : ‖y3‖ ≤ 1 := by

    rw [Affine.equation_iff] at h3
    by_contra hy
    push_neg at hy
    have key : y3 ^ 2 = -((W.a₁ * x3 + W.a₃) * y3) + (x3 ^ 3 + W.a₂ * x3 ^ 2 + W.a₄ * x3 + W.a₆) := by
      linear_combination h3
    have hA : ‖W.a₁ * x3 + W.a₃‖ ≤ 1 := add_le ((mul_le_of_one h1).trans hx3) h3'
    have hx2 : ‖x3‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hx3
    have hB : ‖x3 ^ 3 + W.a₂ * x3 ^ 2 + W.a₄ * x3 + W.a₆‖ ≤ 1 := by
      refine add_le (add_le (add_le ?_ ?_) ?_) h6
      · rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx3
      · exact (mul_le_of_one h2).trans (by rw [norm_pow]; exact hx2)
      · exact (mul_le_of_one h4).trans hx3
    have hR : ‖-((W.a₁ * x3 + W.a₃) * y3) + (x3 ^ 3 + W.a₂ * x3 ^ 2 + W.a₄ * x3 + W.a₆)‖ ≤ ‖y3‖ := by
      refine add_le ?_ (hB.trans hy.le)
      rw [norm_neg, norm_mul]; nlinarith [norm_nonneg (W.a₁ * x3 + W.a₃), norm_nonneg y3]
    rw [← key, norm_pow] at hR
    nlinarith
  set M := max ‖x1‖ ‖x2‖ with hMdef
  have hM1 : 1 < M := lt_max_of_lt_left hX1
  have hs : ‖x1 + x2 + x3‖ ≤ M :=
    add_le (add_le (le_max_left _ _) (le_max_right _ _)) (hx3.trans hM1.le)
  have hL : ‖l‖ ^ 2 ≤ M := lsq h1 h2 hM1.le (by rw [e1]; exact hs)
  have hv : v = y3 - l * x3 := by rw [hy3]; ring
  have hV : ‖v‖ ≤ max 1 ‖l‖ := by
    rw [hv]
    refine sub_le (hy3n.trans (le_max_left _ _)) ?_
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) hx3).trans (le_max_right _ _)
  obtain ⟨hLM, hVM, hLVM⟩ := realC (norm_nonneg _) (norm_nonneg _) hL hM1.le hV
  have hlhs : ‖W.a₄ - 2 * l * v - W.a₁ * v - W.a₃ * l‖ ≤ M := by
    refine sub_le (sub_le (sub_le (h4.trans hM1.le) ?_) ((mul_le_of_one h1).trans hVM))
      ((mul_le_of_one h3').trans hLM)
    rw [mul_assoc]; exact (mul_le_of_one two_le).trans (by rw [norm_mul]; exact hLVM)
  have hprod : M < ‖x1 * x2‖ := by
    rw [norm_mul]
    rcases le_total ‖x1‖ ‖x2‖ with h | h
    · rw [hMdef, max_eq_right h]; nlinarith
    · rw [hMdef, max_eq_left h]; nlinarith
  have hsmall : ‖x3 * (x1 + x2)‖ < ‖x1 * x2‖ := by
    have : ‖x3 * (x1 + x2)‖ ≤ M := by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) hx3 |>.trans
        (add_le (le_max_left _ _) (le_max_right _ _))
    linarith
  have := dom hsmall
  rw [← e2] at this
  linarith
end Formalism.ELL.FormalGroupPointsTorsion
