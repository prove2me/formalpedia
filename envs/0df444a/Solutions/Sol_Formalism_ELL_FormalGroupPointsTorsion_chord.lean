-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsTorsion.chord
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:27:12.344047+00:00
-- url     : https://prove2.me/submissions/618ac50c-4218-4a47-bd83-b69c55809383

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsTorsionFree
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsNoPrimeToPTorsion
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_sub_le
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_sub_lt
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_zfacts
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_negz
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_bigx3
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_sumz

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
theorem _root_.solution [DecidableEq K] (hW : IntegralModel W) {x1 x2 y1 y2 : K}
    (h1 : W.toAffine.Equation x1 y1) (h2 : W.toAffine.Equation x2 y2)
    (hX1 : 1 < ‖x1‖) (hX2 : 1 < ‖x2‖) (hxy : ¬(x1 = x2 ∧ y1 = W.toAffine.negY x2 y2)) :
    1 < ‖W.toAffine.addX x1 x2 (W.toAffine.slope x1 x2 y1 y2)‖ ∧
    ‖W.toAffine.addX x1 x2 (W.toAffine.slope x1 x2 y1 y2) /
        W.toAffine.addY x1 x2 y1 (W.toAffine.slope x1 x2 y1 y2) - x1 / y1 - x2 / y2‖ <
      max ‖x1 / y1‖ ‖x2 / y2‖ := by
  have hp := W.toAffine.addPolynomial_slope h1 h2 hxy
  rw [Affine.addPolynomial_eq, neg_inj, Cubic.prod_X_sub_C_eq, Cubic.toPoly_injective] at hp
  have h3 := W.toAffine.equation_negAdd h1 h2 hxy
  have hl2 : y2 = W.toAffine.slope x1 x2 y1 y2 * (x2 - x1) + y1 := by
    by_cases hx : x1 = x2
    · have hy := Affine.Y_eq_of_Y_ne h1 h2 hx (fun h => hxy ⟨hx, h⟩)
      rw [hx, hy]; ring
    · rw [Affine.slope_of_X_ne hx]
      field_simp [sub_ne_zero.mpr hx]
      ring
  rw [Affine.addY]
  generalize W.toAffine.slope x1 x2 y1 y2 = l at hp h3 hl2 ⊢
  have hx3 : W.toAffine.addX x1 x2 l = l ^ 2 + W.a₁ * l - W.a₂ - x1 - x2 := rfl
  have hy3 : W.toAffine.negAddY x1 x2 y1 l = l * (W.toAffine.addX x1 x2 l - x1) + y1 := rfl
  generalize W.toAffine.negAddY x1 x2 y1 l = y3 at h3 hy3 ⊢
  generalize W.toAffine.addX x1 x2 l = x3 at hp h3 hy3 hx3 ⊢
  simp only [Cubic.mk.injEq] at hp
  obtain ⟨-, -, hc, hd⟩ := hp
  obtain ⟨v, hv⟩ : ∃ v, v = y1 - l * x1 := ⟨_, rfl⟩
  have e1 : l ^ 2 + W.a₁ * l - W.a₂ = x1 + x2 + x3 := by rw [hx3]; ring
  have e2 : W.a₄ - 2 * l * v - W.a₁ * v - W.a₃ * l = x1 * x2 + x3 * (x1 + x2) := by
    rw [hv]; linear_combination hc
  have e3 : v ^ 2 + W.a₃ * v - W.a₆ = x1 * x2 * x3 := by
    rw [hv]; linear_combination -hd
  have hy1' : y1 = l * x1 + v := by rw [hv]; ring
  have hy2' : y2 = l * x2 + v := by rw [hl2, hv]; ring
  have hy3' : y3 = l * x3 + v := by rw [hy3, hv]; ring
  have hX3 := bigx3 hW hX1 hX2 h3 hy3' e1 e2
  refine ⟨hX3, ?_⟩
  have hN : x1 * y2 * y3 + x2 * y1 * y3 + x3 * y1 * y2 =
      -(W.a₁ * (l * v ^ 2)) - W.a₂ * v ^ 2 + W.a₃ * (l ^ 2 * v) + (2 * W.a₄) * (l * v)
        - (3 * W.a₆) * l ^ 2 := by
    rw [hy1', hy2', hy3']
    linear_combination (-3 * l ^ 2) * e3 - (2 * l * v) * e2 - v ^ 2 * e1
  have hs := sumz hW hX1 hX2 hX3 h1 h2 h3 e1 e3 hN
  have hng := negz hW h3 hX3
  obtain ⟨-, ht1, ht1', -⟩ := zfacts hW h1 hX1
  obtain ⟨-, ht2, ht2', -⟩ := zfacts hW h2 hX2
  set S := max ‖x1 / y1‖ ‖x2 / y2‖
  have hS0 : 0 < S := lt_max_of_lt_left ht1
  have hS1 : S < 1 := max_lt ht1' ht2'
  have ht3S : ‖x3 / y3‖ ≤ S := by
    have : x3 / y3 = (x1 / y1 + x2 / y2 + x3 / y3) - x1 / y1 - x2 / y2 := by ring
    rw [this]; exact sub_le (sub_le hs.le (le_max_left _ _)) (le_max_right _ _)
  have hsq : ‖x3 / y3‖ ^ 2 < S := by
    have := pow_le_pow_left₀ (norm_nonneg _) ht3S 2
    nlinarith
  have : x3 / W.toAffine.negY x3 y3 - x1 / y1 - x2 / y2 =
      (x3 / W.toAffine.negY x3 y3 + x3 / y3) - (x1 / y1 + x2 / y2 + x3 / y3) := by ring
  rw [this]
  exact sub_lt (hng.trans_lt hsq) hs
end Formalism.ELL.FormalGroupPointsTorsion
