-- Prove2me | solution 1 for Formalism.L2.Th1.H.IsQuadFn0.symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:39:30.160814+00:00
-- url     : https://prove2.me/submissions/37ae5980-ecd6-48dd-bc59-208a0f9f26ee

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_GaussDegenerate
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_GaussSumEighthPower
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_GapStatement
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
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
open SemicharacterExponentialLemmas
open Formalism.L2.Th1.H.IsQuadFn0
variable {M : Type*} [AddCommGroup M] {φ : M → ℂ} {b : M → M → ℂ}
namespace Formalism.L2.Th1.H.IsQuadFn0
theorem _root_.solution (h : IsQuadFn0 φ b) (x y : M) : b x y = b y x := by
  rw [h.b_eq x y, h.b_eq y x, add_comm y x, mul_comm (φ y)]
end Formalism.L2.Th1.H.IsQuadFn0
