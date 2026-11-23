-- Prove2me | solution 1 for Formalism.ELL.TorsionIntegralEllipticTorsion.y_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:22:10.993788+00:00
-- url     : https://prove2.me/submissions/0c665d30-e682-4652-a50e-3e855e799063

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsTorsionFree
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_TorInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.TorsionIntegralEllipticTorsion
open WeierstrassCurve Formalism.ELL
namespace Formalism.ELL.TorsionIntegralEllipticTorsion
theorem _root_.solution {K : Type u} [NormedField K] [IsUltrametricDist K] (W : WeierstrassCurve K)
    (hW : IntegralModel W) {x y : K} (h : W.toAffine.Equation x y) (hx : ‖x‖ ≤ 1) :
    ‖y‖ ≤ 1 := by
  have hW' := hW
  unfold IntegralModel at hW'
  have h' := h
  rw [WeierstrassCurve.Affine.equation_iff] at h'
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW'
  have hadd : ∀ a b : K, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖a + b‖ ≤ 1 := fun a b ha hb =>
    (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  have hmul : ∀ a b : K, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖a * b‖ ≤ 1 := fun a b ha hb => by
    rw [norm_mul]
    first
    | exact mul_le_one₀ ha (norm_nonneg _) hb
    | nlinarith [norm_nonneg a, norm_nonneg b]
  have hx2 : ‖x ^ 2‖ ≤ 1 := by
    rw [norm_pow]
    first
    | exact pow_le_one₀ (norm_nonneg _) hx
    | nlinarith [norm_nonneg x]
  have hx3 : ‖x ^ 3‖ ≤ 1 := by
    rw [norm_pow]
    first
    | exact pow_le_one₀ (norm_nonneg _) hx
    | nlinarith [norm_nonneg x, hx2]
  have hR : ‖x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆‖ ≤ 1 :=
    hadd _ _ (hadd _ _ (hadd _ _ hx3 (hmul _ _ h2 hx2)) (hmul _ _ h4 hx)) h6
  by_contra hy
  push_neg at hy
  have hy0 : 0 ≤ ‖y‖ := norm_nonneg _
  have hm : ‖W.a₁ * x * y + W.a₃ * y‖ ≤ ‖y‖ := by
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      calc ‖W.a₁ * x‖ * ‖y‖ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right (hmul _ _ h1 hx) hy0
        _ = ‖y‖ := one_mul _
    · rw [norm_mul]
      calc ‖W.a₃‖ * ‖y‖ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right h3 hy0
        _ = ‖y‖ := one_mul _
  have hy2 : y ^ 2 = (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) - (W.a₁ * x * y + W.a₃ * y) := by
    first
    | linear_combination h'
    | (rw [← h']; ring)
  have hsub : ‖(x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) - (W.a₁ * x * y + W.a₃ * y)‖ ≤ ‖y‖ := by
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hR.trans hy.le) ?_)
    rw [norm_neg]
    exact hm
  have hn : ‖y‖ ^ 2 ≤ ‖y‖ := by
    rw [← norm_pow, hy2]
    exact hsub
  nlinarith
end Formalism.ELL.TorsionIntegralEllipticTorsion
