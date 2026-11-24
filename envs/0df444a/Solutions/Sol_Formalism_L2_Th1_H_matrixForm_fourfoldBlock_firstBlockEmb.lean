-- Prove2me | solution 1 for Formalism.L2.Th1.H.matrixForm_fourfoldBlock_firstBlockEmb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:27:14.701584+00:00
-- url     : https://prove2.me/submissions/0ddaaa75-df19-4ad7-ac6e-0a877a5efb78

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_LineTransport
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlockFirstBlockEmb
import Theorems.Thm_Formalism_L2_Th1_H_blockSlice_firstBlockEmb
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
variable {n : Type*} [Fintype n]
namespace Formalism.L2.Th1.H
theorem _root_.solution (h : Matrix n n ℂ) (z : Fin 4 × n → ℂ) (x : n → ℂ) :
    matH (blk4 h) z (emb0 x) = matH h (slice 0 z) x := by
  rw [matrixForm_fourfoldBlock, Finset.sum_eq_single (0 : Fin 4)]
  · rw [blockSlice_firstBlockEmb, if_pos rfl]
  · intro a _ ha
    rw [blockSlice_firstBlockEmb, if_neg ha, map_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h
end Formalism.L2.Th1.H
