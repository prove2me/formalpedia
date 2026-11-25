-- Prove2me | solution 1 for Formalism.L2.Th1.H.heisenbergNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:16:19.884951+00:00
-- url     : https://prove2.me/submissions/cc171c98-ca64-4180-b1a5-11472434af93

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_SemiCharBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Theorems.Thm_Formalism_L2_Th1_H_re_swap

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
theorem _root_.solution : OpUNorm := by
  intro V _ _ H hH x F z
  have hre := re_swap H hH z x
  have hE : (-(Real.pi : ℂ) * H z x - (Real.pi : ℂ) * H x x / 2).re =
      -Real.pi * (H z x).re - Real.pi * (H x x).re / 2 := by
    simp [Complex.sub_re, Complex.mul_re]
  have hzz : (H (z + x) (z + x)).re = (H z z).re + 2 * (H z x).re + (H x x).re := by
    simp only [map_add, LinearMap.add_apply, Complex.add_re]
    linarith
  simp only [opU, norm_mul, Complex.norm_exp, hE]
  rw [hzz, mul_pow, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
  congr 2
  push_cast
  ring
end Formalism.L2.Th1.H
