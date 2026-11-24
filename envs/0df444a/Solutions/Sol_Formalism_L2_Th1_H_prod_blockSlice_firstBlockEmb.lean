-- Prove2me | solution 1 for Formalism.L2.Th1.H.prod_blockSlice_firstBlockEmb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:27:31.650223+00:00
-- url     : https://prove2.me/submissions/89c39937-67a9-4289-bca5-906f2553ee1f

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_LineTransport
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlockFirstBlockEmb
import Theorems.Thm_Formalism_L2_Th1_H_blockSlice_firstBlockEmb

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
theorem _root_.solution (α : (n → ℂ) → ℂ) (hα0 : α 0 = 1) (x : n → ℂ) :
    ∏ a, α (slice a (emb0 x)) = α x := by
  rw [Finset.prod_eq_single (0 : Fin 4)]
  · rw [blockSlice_firstBlockEmb, if_pos rfl]
  · intro a _ ha
    rw [blockSlice_firstBlockEmb, if_neg ha, hα0]
  · intro h
    exact absurd (Finset.mem_univ _) h
end Formalism.L2.Th1.H
