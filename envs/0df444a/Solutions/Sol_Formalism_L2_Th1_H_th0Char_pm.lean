-- Prove2me | solution 1 for Formalism.L2.Th1.H.th0Char_pm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:34:02.727805+00:00
-- url     : https://prove2.me/submissions/e9e14f58-893b-4f6e-bbca-0d050ff60a3b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstIsogeny
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Th0TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_Th0CharMulOpUTh0HalfPeriodEq
import Theorems.Thm_Formalism_L2_Th1_H_exp_pi_int
import Theorems.Thm_Formalism_L2_Th1_H_neg_one_zpow_pm
import Theorems.Thm_Formalism_L2_Th1_H_semiChar_pm
import Theorems.Thm_Formalism_L2_Th1_F_Cm2_exp_pi_int
import Theorems.Thm_Formalism_L2_Th1_F_PeriodAreaSignLemmas_exp_pi_int
import Theorems.Thm_Formalism_L2_Th1_F_ThetaZeroHermitianLemmas_exp_pi_int
import Theorems.Thm_Formalism_L2_Th1_F_altEInt


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
theorem _root_.solution (L : PeriodPair) (ω₀ ω : ℂ) (h0 : ω₀ ∈ L.lattice) (h : ω ∈ L.lattice) :
    Formalism.L2.Th1.F.thetaZeroCharacter L ω₀ ω = 1 ∨ Formalism.L2.Th1.F.thetaZeroCharacter L ω₀ ω = -1 := by
  obtain ⟨k, hk⟩ := Formalism.L2.Th1.F.altEInt L ω ω₀ h h0
  rw [Formalism.L2.Th1.F.thetaZeroCharacter, hk, exp_pi_int]
  rcases semiChar_pm L ω with h1 | h1 <;> rcases neg_one_zpow_pm k with h2 | h2 <;> rw [h1, h2] <;>
    norm_num
end Formalism.L2.Th1.H
