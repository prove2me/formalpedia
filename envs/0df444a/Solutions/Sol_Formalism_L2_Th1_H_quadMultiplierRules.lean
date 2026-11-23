-- Prove2me | solution 1 for Formalism.L2.Th1.H.quadMultiplierRules
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:11:42.908293+00:00
-- url     : https://prove2.me/submissions/a6855f57-4368-48dd-a830-c6ae575ad2a3

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_LineTransport
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlockFirstBlockEmb
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
theorem _root_.solution : AlphaQRules := by
  refine ⟨?_, ?_⟩
  · intro V W _ _ _ _ H H' g hg c x
    simp only [alphaQ, qOf, hg x x]
  · intro n _ h c x
    simp only [alphaQ, qOf, matrixForm_fourfoldBlock]
    rw [← Complex.exp_sum]
    congr 1
    rw [Complex.re_sum, Finset.mul_sum, Complex.ofReal_sum, Finset.mul_sum]
end Formalism.L2.Th1.H
