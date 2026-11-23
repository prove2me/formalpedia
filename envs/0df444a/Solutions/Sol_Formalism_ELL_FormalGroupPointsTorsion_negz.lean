-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsTorsion.negz
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:15:55.614563+00:00
-- url     : https://prove2.me/submissions/1e5576f8-571d-483b-a174-02980ae9278f

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsTorsionFree
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsNoPrimeToPTorsion
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_add_le
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_dom
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_mul_le_of_one
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_vy

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
    ‖x / W.toAffine.negY x y + x / y‖ ≤ ‖x / y‖ ^ 2 := by
  obtain ⟨hy2, hxy⟩ := vy hW h hx
  have hy0 : y ≠ 0 := norm_pos_iff.mp (by linarith)
  have hc : ‖W.a₁ * x + W.a₃‖ ≤ ‖x‖ := add_le (mul_le_of_one hW.1) (hW.2.2.1.trans hx.le)
  have hn : W.toAffine.negY x y = -y + -(W.a₁ * x + W.a₃) := by
    simp only [Affine.negY]; ring
  have hnn : ‖W.toAffine.negY x y‖ = ‖y‖ := by
    have : ‖-(W.a₁ * x + W.a₃)‖ < ‖-y‖ := by rw [norm_neg, norm_neg]; linarith
    rw [hn, dom this, norm_neg]
  have hn0 : W.toAffine.negY x y ≠ 0 := norm_pos_iff.mp (by rw [hnn]; linarith)
  rw [div_add_div _ _ hn0 hy0]
  have : x * y + W.toAffine.negY x y * x = x * (-(W.a₁ * x + W.a₃)) := by rw [hn]; ring
  rw [this, norm_div, norm_mul, norm_mul, norm_neg, hnn, norm_div, div_pow, sq, sq]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left hc (norm_nonneg _)
end Formalism.ELL.FormalGroupPointsTorsion
