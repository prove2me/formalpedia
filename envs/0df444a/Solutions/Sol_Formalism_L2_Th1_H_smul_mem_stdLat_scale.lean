-- Prove2me | solution 1 for Formalism.L2.Th1.H.smul_mem_stdLat_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:00:53.658799+00:00
-- url     : https://prove2.me/submissions/618fd6e8-6b31-4511-a400-97b023684737

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_QuadraticSemicharactersFactAltForm
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_Th0CharMulOpUTh0HalfPeriodEq
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ScalePairMulMulEq
import Theorems.Thm_Formalism_L2_Th1_H_mul_mem_scale
import Theorems.Thm_Formalism_L2_Th1_H_mem_stdLat


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
theorem _root_.solution (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (n : Type*) (x : n → ℂ) :
    c • x ∈ stdLat (scalePair L c hc) n ↔ x ∈ stdLat L n := by
  simp only [mem_stdLat, Pi.smul_apply, smul_eq_mul, mul_mem_scale]
end Formalism.L2.Th1.H
