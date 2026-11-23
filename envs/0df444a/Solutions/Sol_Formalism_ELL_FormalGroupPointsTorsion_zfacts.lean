-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsTorsion.zfacts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:13:19.641463+00:00
-- url     : https://prove2.me/submissions/12cd40f9-fedd-4bd1-8347-6e5380634a9d

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsTorsionFree
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsNoPrimeToPTorsion
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
    y ≠ 0 ∧ 0 < ‖x / y‖ ∧ ‖x / y‖ < 1 ∧ ‖x / y‖ ^ 2 * ‖x‖ = 1 := by
  obtain ⟨hy2, hxy⟩ := vy hW h hx
  have hYp : 0 < ‖y‖ := by linarith
  have hy0 : y ≠ 0 := norm_pos_iff.mp hYp
  refine ⟨hy0, ?_, ?_, ?_⟩
  · rw [norm_div]; exact div_pos (by linarith) hYp
  · rw [norm_div, div_lt_one hYp]; exact hxy
  · rw [norm_div, div_pow]
    field_simp
    nlinarith [hy2]
end Formalism.ELL.FormalGroupPointsTorsion
