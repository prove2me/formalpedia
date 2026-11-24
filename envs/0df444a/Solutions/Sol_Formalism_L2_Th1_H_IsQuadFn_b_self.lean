-- Prove2me | solution 1 for Formalism.L2.Th1.H.IsQuadFn.b_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:26:13.994793+00:00
-- url     : https://prove2.me/submissions/dd6b74b5-abdc-485b-8155-1a9ac9251f09

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_UnitaryConstant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_GaussSumEighthPower

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
theorem _root_.solution (h : IsQuadFn φ b) (x : M) : b x x = φ x ^ 2 := by
  have hx := h.ne x
  have h1 := h.sq 2 x
  rw [two_nsmul, h.add] at h1
  apply mul_left_cancel₀ (mul_ne_zero hx hx)
  rw [h1]
  ring
end Formalism.L2.Th1.H.IsQuadFn
