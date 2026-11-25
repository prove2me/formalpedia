-- Prove2me | solution 1 for Formalism.L2.Th1.H.mul_mem_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:28:47.367675+00:00
-- url     : https://prove2.me/submissions/902205dc-994d-4626-b6ec-a771d3a6478d

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_QuadraticSemicharactersFactAltForm
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_Th0CharMulOpUTh0HalfPeriodEq
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ScalePairMulMulEq
import Theorems.Thm_Formalism_L2_Th1_F_homogeneity


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
open Formalism.L2.Th1.F (scalePair)
namespace Formalism.L2.Th1.H
theorem _root_.solution (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (z : ℂ) :
    c * z ∈ (scalePair L c hc).lattice ↔ z ∈ L.lattice := by
  rw [(Formalism.L2.Th1.F.homogeneity L c hc).1, inv_mul_cancel_left₀ hc]
end Formalism.L2.Th1.H
