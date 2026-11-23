-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsTorsion.lsq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:12:39.507924+00:00
-- url     : https://prove2.me/submissions/b82b5af9-74e2-4da1-a30f-6770f903a538

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsTorsionFree
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsNoPrimeToPTorsion
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_sub_le
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
theorem _root_.solution {l a b : K} {M : ℝ} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hM : 1 ≤ M)
    (h : ‖l ^ 2 + a * l - b‖ ≤ M) : ‖l‖ ^ 2 ≤ M := by
  by_cases hL : ‖l‖ ≤ 1
  · exact (pow_le_one₀ (norm_nonneg _) hL).trans hM
  · push_neg at hL
    have h1 : ‖a * l - b‖ < ‖l ^ 2‖ := by
      have : ‖a * l - b‖ ≤ ‖l‖ := sub_le (mul_le_of_one ha) (hb.trans hL.le)
      rw [norm_pow]; nlinarith
    rw [add_sub_assoc, dom h1, norm_pow] at h
    exact h
end Formalism.ELL.FormalGroupPointsTorsion
