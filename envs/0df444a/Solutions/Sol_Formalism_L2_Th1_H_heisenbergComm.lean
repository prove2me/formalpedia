-- Prove2me | solution 1 for Formalism.L2.Th1.H.heisenbergComm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:32:21.228987+00:00
-- url     : https://prove2.me/submissions/09b4f7d8-cd66-4804-b3ba-4b316ec880b4

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_SemiCharBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Theorems.Thm_Formalism_L2_Th1_H_altE_swap
import Theorems.Thm_Formalism_L2_Th1_H_heisenbergMul
import Theorems.Thm_Formalism_L2_Th1_F_OperatorUThetaLemmas_altE_swap


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
theorem _root_.solution : OpUComm := by
  intro V _ _ H hH F z
  refine ⟨by simp [opU], fun x y => ?_⟩
  have h1 := heisenbergMul V H hH x y F z
  have h2 := heisenbergMul V H hH y x F z
  rw [add_comm y x, altE_swap H hH] at h2
  rw [h1, h2, ← mul_assoc, ← Complex.exp_add]
  congr 1
  congr 1
  push_cast
  ring
end Formalism.L2.Th1.H
