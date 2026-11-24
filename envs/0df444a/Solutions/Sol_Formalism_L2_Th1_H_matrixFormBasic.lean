-- Prove2me | solution 1 for Formalism.L2.Th1.H.matrixFormBasic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:27:13.323213+00:00
-- url     : https://prove2.me/submissions/88b2b057-ab5a-47ec-ae11-d56778550e5c

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_SemiCharBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Theorems.Thm_Formalism_L2_Th1_H_matH_apply

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
theorem _root_.solution : MatHBasic := by
  intro n _ h
  refine ⟨fun z w => rfl, fun hh x y => ?_⟩
  rw [matH_apply, matH_apply, map_sum]
  simp_rw [map_sum, map_mul, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hc : conj (h i j) = h j i := by
    have h' := congrFun (congrFun hh j) i
    simpa [Matrix.conjTranspose_apply] using h'
  rw [hc]
  ring
end Formalism.L2.Th1.H
