-- Prove2me | solution 1 for Formalism.L2.Th1.H.fourfoldTensorMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:41:12.692233+00:00
-- url     : https://prove2.me/submissions/3d4f20da-528f-43e2-8fa6-82c5d6b7df52

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_LineTransport
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlockFirstBlockEmb
import Theorems.Thm_Formalism_L2_Th1_H_slice_analyticAt
import Theorems.Thm_Formalism_L2_Th1_H_heisenbergFourfold


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
theorem _root_.solution : Tens4Mem := by
  intro n _ h Λ α θ hθ
  refine ⟨?_, ?_⟩
  · intro z _
    refine Finset.analyticAt_fun_prod _ fun a _ => ?_
    exact ((hθ a).1 (slice a z) (Set.mem_univ _)).comp_of_eq (slice_analyticAt a z) rfl
  · intro x hx z
    rw [(heisenbergFourfold n h).2 x θ z]
    show (∏ a, α (slice a x)) * _ = ∏ a, θ a (slice a z)
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun a _ => (hθ a).2 (slice a x) (hx a) (slice a z)
end Formalism.L2.Th1.H
