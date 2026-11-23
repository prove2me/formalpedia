-- Prove2me | solution 1 for Formalism.L2.Th1.H.IsQuadFn.b_neg_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:20:57.208623+00:00
-- url     : https://prove2.me/submissions/67d8bf51-fea4-4ba0-a6ff-56db863800cc

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_UnitaryConstant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_GaussSumEighthPower
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
theorem _root_.solution (h : IsQuadFn φ b) (x y : M) : b (-x) y = (b x y)⁻¹ := by
  have h1 : b (-x) y * b x y = 1 := by
    rw [← h.left, show -x + x = (0 : M) by simp, h.b_zero_left]
  exact eq_inv_of_mul_eq_one_left h1
end Formalism.L2.Th1.H.IsQuadFn
