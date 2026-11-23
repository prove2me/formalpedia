-- Prove2me | solution 1 for Formalism.L2.Th1.H.heisenbergFourfold
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:48.951021+00:00
-- url     : https://prove2.me/submissions/b7e751a1-8181-4172-a51c-668b05a5ca3b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_SemiCharBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Theorems.Thm_Formalism_L2_Th1_H_matrixForm_fourfoldBlock

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
namespace Formalism.L2.Th1.H
theorem _root_.solution : OpUBlk4 := by
  intro n _ h
  refine ⟨matrixForm_fourfoldBlock h, fun x θ z => ?_⟩
  simp only [opU, matrixForm_fourfoldBlock]
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum, Finset.mul_sum, Finset.mul_sum, Finset.sum_div,
    ← Finset.sum_sub_distrib]
  rfl
end Formalism.L2.Th1.H
