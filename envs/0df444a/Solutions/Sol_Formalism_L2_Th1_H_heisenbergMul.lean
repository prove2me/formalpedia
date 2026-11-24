-- Prove2me | solution 1 for Formalism.L2.Th1.H.heisenbergMul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:27:20.266878+00:00
-- url     : https://prove2.me/submissions/19cc0219-df6a-40af-9de2-2a0e0ddc1219

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_SemiCharBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Theorems.Thm_Formalism_L2_Th1_H_herm_sub_swap
import Theorems.Thm_Formalism_L2_Th1_F_ThetaZeroHermitianLemmas_herm_sub_swap


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
theorem _root_.solution : OpUMul := by
  intro V _ _ H hH x y F z
  have hs := herm_sub_swap H hH x y
  simp only [opU]
  rw [mul_assoc, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add, add_assoc z x y]
  congr 2
  simp only [map_add, LinearMap.add_apply]
  linear_combination (-(Real.pi : ℂ) / 2) * hs
end Formalism.L2.Th1.H
