-- Prove2me | solution 1 for Formalism.L2.Th1.H.heisenbergStandard
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:49.502495+00:00
-- url     : https://prove2.me/submissions/eae8c87c-0263-408f-8605-b157dd5465b1

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_SemiCharBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Theorems.Thm_Formalism_L2_Th1_H_stdH_apply

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
theorem _root_.solution : OpUStd := by
  intro L n _ _ x f z
  simp only [opU, Formalism.L2.Th1.F.opU, prodFn, stdH_apply, Pi.add_apply]
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum, Finset.mul_sum, Finset.mul_sum, Finset.sum_div,
    ← Finset.sum_sub_distrib]
end Formalism.L2.Th1.H
