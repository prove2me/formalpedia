-- Prove2me | solution 1 for Formalism.L2.Th1.H.IsQuadFn.b_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:13:19.599002+00:00
-- url     : https://prove2.me/submissions/1267b555-2ab9-4f7f-b5c9-2e38c8d00a41

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
theorem _root_.solution (h : IsQuadFn φ b) (x y : M) : b x y = φ (x + y) / (φ x * φ y) := by
  exact eq_div_of_mul_eq (mul_ne_zero (h.ne x) (h.ne y)) (by rw [h.add]; ring)
end Formalism.L2.Th1.H.IsQuadFn
