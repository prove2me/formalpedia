-- Prove2me | solution 1 for Formalism.L2.Th1.H.IsQuadFn.b_nsmul_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:39:05.214162+00:00
-- url     : https://prove2.me/submissions/4c5a449e-e7a5-418a-a377-688f57ca8057

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_UnitaryConstant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_GaussSumEighthPower
import Theorems.Thm_Formalism_L2_Th1_H_IsQuadFn_symm
import Theorems.Thm_Formalism_L2_Th1_H_IsQuadFn_b_nsmul_left

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
theorem _root_.solution (h : IsQuadFn φ b) (k l : ℕ) (x y : M) :
    b (k • x) (l • y) = b x y ^ (k * l) := by
  rw [h.b_nsmul_left, h.symm x (l • y), h.b_nsmul_left, h.symm y x,
    ← pow_mul, mul_comm l k]
end Formalism.L2.Th1.H.IsQuadFn
