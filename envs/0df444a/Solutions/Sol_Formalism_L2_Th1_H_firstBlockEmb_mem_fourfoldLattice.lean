-- Prove2me | solution 1 for Formalism.L2.Th1.H.firstBlockEmb_mem_fourfoldLattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:26:15.139524+00:00
-- url     : https://prove2.me/submissions/721a219e-a6e6-4af7-8250-474266d9ce02

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
theorem _root_.solution (Λ : AddSubgroup (n → ℂ)) {x : n → ℂ} (hx : x ∈ Λ) : emb0 x ∈ pow4 Λ := by
  intro a
  rw [blockSlice_firstBlockEmb]
  split_ifs
  · exact hx
  · exact Λ.zero_mem
end Formalism.L2.Th1.H
