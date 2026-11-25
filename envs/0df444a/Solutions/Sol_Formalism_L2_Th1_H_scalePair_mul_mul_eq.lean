-- Prove2me | solution 1 for Formalism.L2.Th1.H.scalePair_mul_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:50:22.664946+00:00
-- url     : https://prove2.me/submissions/c0438ce9-716a-4495-aa79-7e5bb4b89ad7

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_QuadraticSemicharactersFactAltForm
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_Th0CharMulOpUTh0HalfPeriodEq
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ScalePairMulMulEq
import Theorems.Thm_Formalism_L2_Th1_H_herm_scale
import Theorems.Thm_Formalism_L2_Th1_F_Homog_herm_scale


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
theorem _root_.solution (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (z w : ℂ) :
    Formalism.L2.Th1.F.altE (scalePair L c hc) (c * z) (c * w) = Formalism.L2.Th1.F.altE L z w := by
  simp only [Formalism.L2.Th1.F.altE, herm_scale]
end Formalism.L2.Th1.H
