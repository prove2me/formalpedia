-- Prove2me | solution 1 for Formalism.L2.Th1.H.IsQuadFn.b_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:26:11.030061+00:00
-- url     : https://prove2.me/submissions/aef98858-e225-4426-b4bc-298368055c2a

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_UnitaryConstant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_GaussSumEighthPower
import Theorems.Thm_Formalism_L2_Th1_H_IsQuadFn_b_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
open Formalism.L2.Th1.H.IsQuadFn
variable {M : Type*} [AddCommGroup M] {φ : M → ℂ} {b : M → M → ℂ}
namespace Formalism.L2.Th1.H.IsQuadFn
theorem _root_.solution (h : IsQuadFn φ b) (x y : M) : b x y ≠ 0 := by
  rw [h.b_eq]
  exact div_ne_zero (h.ne _) (mul_ne_zero (h.ne x) (h.ne y))
end Formalism.L2.Th1.H.IsQuadFn
