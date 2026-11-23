-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsTorsion.sumz
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:23:11.912198+00:00
-- url     : https://prove2.me/submissions/708f0f01-a89a-4aa0-b375-5117f66abbfd

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsTorsionFree
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsNoPrimeToPTorsion
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_add_le
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_sub_le
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_add_lt
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_sub_lt
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_dom
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_mul_le_of_one
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_two_le
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_three_le
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_vy
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_zfacts
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_lsq
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_realB

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
theorem _root_.solution (hW : IntegralModel W) {x1 x2 x3 y1 y2 y3 l v : K}
    (hX1 : 1 < ‖x1‖) (hX2 : 1 < ‖x2‖) (hX3 : 1 < ‖x3‖)
    (hE1 : W.toAffine.Equation x1 y1) (hE2 : W.toAffine.Equation x2 y2)
    (hE3 : W.toAffine.Equation x3 y3)
    (e1 : l ^ 2 + W.a₁ * l - W.a₂ = x1 + x2 + x3)
    (e3 : v ^ 2 + W.a₃ * v - W.a₆ = x1 * x2 * x3)
    (hN : x1 * y2 * y3 + x2 * y1 * y3 + x3 * y1 * y2 =
      -(W.a₁ * (l * v ^ 2)) - W.a₂ * v ^ 2 + W.a₃ * (l ^ 2 * v) + (2 * W.a₄) * (l * v)
        - (3 * W.a₆) * l ^ 2) :
    ‖x1 / y1 + x2 / y2 + x3 / y3‖ < max ‖x1 / y1‖ ‖x2 / y2‖ := by
  obtain ⟨hy10, ht1, ht1', hq1⟩ := zfacts hW hE1 hX1
  obtain ⟨hy20, ht2, ht2', hq2⟩ := zfacts hW hE2 hX2
  obtain ⟨hy30, -, -, -⟩ := zfacts hW hE3 hX3
  have hY1 := (vy hW hE1 hX1).1
  have hY2 := (vy hW hE2 hX2).1
  have hY3 := (vy hW hE3 hX3).1
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW

  have hP : 1 < ‖x1 * x2 * x3‖ := by
    rw [norm_mul, norm_mul]
    have : 1 < ‖x1‖ * ‖x2‖ := by nlinarith
    nlinarith
  have hV1 : 1 < ‖v‖ := by
    by_contra hc; push_neg at hc
    have : ‖v ^ 2 + W.a₃ * v - W.a₆‖ ≤ 1 :=
      sub_le (add_le (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hc)
        ((mul_le_of_one h3).trans hc)) h6
    rw [e3] at this; linarith
  have hV : ‖v‖ ^ 2 = ‖x1‖ * ‖x2‖ * ‖x3‖ := by
    have hlt : ‖W.a₃ * v - W.a₆‖ < ‖v ^ 2‖ := by
      have : ‖W.a₃ * v - W.a₆‖ ≤ ‖v‖ := sub_le (mul_le_of_one h3) (h6.trans hV1.le)
      rw [norm_pow]; nlinarith
    have := dom hlt
    rw [← add_sub_assoc, e3, norm_pow, norm_mul, norm_mul] at this
    exact this.symm

  have hL : ‖l‖ ^ 2 ≤ max (max ‖x1‖ ‖x2‖) ‖x3‖ := by
    refine lsq h1 h2 ((hX1.le.trans (le_max_left _ _)).trans (le_max_left _ _)) ?_
    rw [e1]
    refine add_le (add_le ?_ ?_) (le_max_right _ _)
    · exact (le_max_left _ _).trans (le_max_left _ _)
    · exact (le_max_right _ _).trans (le_max_left _ _)
  obtain ⟨hSV, hLSV⟩ := realB ht1 ht2 hq1 hq2 hX1 hX2 hX3 (norm_nonneg _) hV (norm_nonneg _) hL
  set S := max ‖x1 / y1‖ ‖x2 / y2‖ with hSdef
  have hS0 : 0 < S := lt_max_of_lt_left ht1
  have hS1 : S < 1 := max_lt ht1' ht2'

  have hYp : ‖y1 * y2 * y3‖ = ‖v‖ ^ 3 := by
    rw [norm_mul, norm_mul]
    rw [← pow_left_inj₀ (by positivity) (by positivity) (two_ne_zero)]
    rw [mul_pow, mul_pow, hY1, hY2, hY3]
    have : (‖v‖ ^ 3) ^ 2 = (‖v‖ ^ 2) ^ 3 := by ring
    rw [this, hV]; ring
  set V := ‖v‖
  set L := ‖l‖
  have hV0 : 0 < V := by linarith
  have hB : ‖x1 * y2 * y3 + x2 * y1 * y3 + x3 * y1 * y2‖ < S * V ^ 3 := by
    rw [hN]
    have hLV : L * V < S * V * V := mul_lt_mul_of_pos_right hLSV hV0
    have hL2 : L ^ 2 < (S * V) ^ 2 := pow_lt_pow_left₀ hLSV (norm_nonneg _) two_ne_zero
    have hS1' : S ≤ V := by linarith
    have hSV2 : S * S * V ^ 2 ≤ S * V ^ 3 := by
      have : S * S * V ^ 2 ≤ S * V * V ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hS1' hS0.le) (by positivity)
      linarith [show S * V * V ^ 2 = S * V ^ 3 by ring]
    have h2a4 : ‖2 * W.a₄‖ ≤ 1 := by
      rw [norm_mul]; exact mul_le_one₀ two_le (norm_nonneg _) h4
    have h3a6 : ‖3 * W.a₆‖ ≤ 1 := by
      rw [norm_mul]; exact mul_le_one₀ three_le (norm_nonneg _) h6
    refine sub_lt (add_lt (add_lt (sub_lt ?_ ?_) ?_) ?_) ?_
    · rw [norm_neg]
      refine (mul_le_of_one h1).trans_lt ?_
      rw [norm_mul, norm_pow]
      have := mul_lt_mul_of_pos_right hLSV (pow_pos hV0 2)
      linarith [show S * V * V ^ 2 = S * V ^ 3 by ring]
    · refine (mul_le_of_one h2).trans_lt ?_
      rw [norm_pow]
      have := mul_lt_mul_of_pos_right hSV (pow_pos hV0 2)
      linarith [show S * V * V ^ 2 = S * V ^ 3 by ring]
    · refine (mul_le_of_one h3).trans_lt ?_
      rw [norm_mul, norm_pow]
      have := mul_lt_mul_of_pos_right hL2 hV0
      linarith [show (S * V) ^ 2 * V = S * S * V ^ 2 * V by ring,
        mul_le_mul_of_nonneg_right hSV2 hV0.le, show S * V ^ 3 * V = S * V ^ 3 * V by ring,
        show S * S * V ^ 2 * V ≤ S * V ^ 3 * 1 by
          have : S * S * V ^ 2 * V ≤ S * S * V ^ 2 * V := le_rfl
          nlinarith [mul_pos hS0 hS0, pow_pos hV0 3]]
    · refine (mul_le_of_one h2a4).trans_lt ?_
      rw [norm_mul]
      have : S * V * V ≤ S * V * V * V := le_mul_of_one_le_right (by positivity) hV1.le
      linarith [show S * V * V * V = S * V ^ 3 by ring]
    · refine (mul_le_of_one h3a6).trans_lt ?_
      rw [norm_pow]
      linarith [show (S * V) ^ 2 = S * S * V ^ 2 by ring]
  have hsum : x1 / y1 + x2 / y2 + x3 / y3 =
      (x1 * y2 * y3 + x2 * y1 * y3 + x3 * y1 * y2) / (y1 * y2 * y3) := by
    field_simp
  rw [hsum, norm_div, hYp, div_lt_iff₀ (by positivity)]
  exact hB
end Formalism.ELL.FormalGroupPointsTorsion
