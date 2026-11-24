-- Prove2me | solution 1 for Formalism.L2.Th1.H.IsQuadFn.b_zero_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:26:15.080095+00:00
-- url     : https://prove2.me/submissions/40107985-810a-4b3a-814b-87154e769edb

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_UnitaryConstant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_GaussSumEighthPower
import Theorems.Thm_Formalism_L2_Th1_H_IsQuadFn_symm
import Theorems.Thm_Formalism_L2_Th1_H_IsQuadFn_b_zero_left

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
theorem _root_.solution (h : IsQuadFn φ b) (y : M) : b y 0 = 1 := by
  rw [h.symm, h.b_zero_left]
end Formalism.L2.Th1.H.IsQuadFn
