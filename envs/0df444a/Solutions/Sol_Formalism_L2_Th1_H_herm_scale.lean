-- Prove2me | solution 1 for Formalism.L2.Th1.H.herm_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:26:43.870684+00:00
-- url     : https://prove2.me/submissions/c0dfa784-ee0e-4803-a974-3024a77b7446

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
theorem _root_.solution (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (z w : ℂ) :
    Formalism.L2.Th1.F.herm (scalePair L c hc) (c * z) (c * w) = Formalism.L2.Th1.F.herm L z w := by
  have hA := (Formalism.L2.Th1.F.homogeneity L c hc).2.2.2.2.2.1
  have hn : ((‖c‖ : ℂ)) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast (norm_pos_iff.mpr hc).ne')
  simp only [Formalism.L2.Th1.F.herm, hA, map_mul]
  have h1 : c * z * (conj c * conj w) = (‖c‖ : ℂ) ^ 2 * (z * conj w) := by
    rw [← Complex.mul_conj' c]; ring
  rw [h1]
  push_cast
  exact mul_div_mul_left _ _ hn
end Formalism.L2.Th1.H
