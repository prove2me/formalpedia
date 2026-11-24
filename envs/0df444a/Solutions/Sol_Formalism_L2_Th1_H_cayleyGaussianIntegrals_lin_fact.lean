-- Prove2me | solution 1 for Formalism.L2.Th1.H.cayleyGaussianIntegrals_lin_fact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:26:17.379848+00:00
-- url     : https://prove2.me/submissions/d07139d7-635e-4835-8425-b6672a17a7bb

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstIsogeny
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Th0TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_Th0CharMulOpUTh0HalfPeriodEq

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
theorem _root_.solution (L : PeriodPair) (s t : ℝ) (a b c : ℂ) :
    Formalism.L2.Th1.F.altE L ((s : ℂ) * a + (t : ℂ) * b) c
      = s * Formalism.L2.Th1.F.altE L a c + t * Formalism.L2.Th1.F.altE L b c := by
  have h : Formalism.L2.Th1.F.herm L ((s : ℂ) * a + (t : ℂ) * b) c
      = (s : ℂ) * Formalism.L2.Th1.F.herm L a c + (t : ℂ) * Formalism.L2.Th1.F.herm L b c := by
    simp only [Formalism.L2.Th1.F.herm]
    ring
  rw [Formalism.L2.Th1.F.altE, h, Complex.add_im, Complex.im_ofReal_mul, Complex.im_ofReal_mul]
  rfl
end Formalism.L2.Th1.H
