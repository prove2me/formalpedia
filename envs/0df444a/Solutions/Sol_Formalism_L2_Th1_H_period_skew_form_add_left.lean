-- Prove2me | solution 1 for Formalism.L2.Th1.H.period_skew_form_add_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:27:28.213338+00:00
-- url     : https://prove2.me/submissions/1066fc39-e851-4846-a6c0-9d47241217e2

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstIsogeny
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Th0TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_Th0CharMulOpUTh0HalfPeriodEq
import Theorems.Thm_Formalism_L2_Th1_F_OperatorUThetaLemmas_herm_add_left
import Theorems.Thm_Formalism_L2_Th1_F_ThetaZeroHermitianLemmas_herm_add_left


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
theorem _root_.solution (L : PeriodPair) (a b c : ℂ) :
    Formalism.L2.Th1.F.altE L (a + b) c = Formalism.L2.Th1.F.altE L a c + Formalism.L2.Th1.F.altE L b c := by
  rw [Formalism.L2.Th1.F.altE, Formalism.L2.Th1.F.OperatorUThetaLemmas.herm_add_left, Complex.add_im]
  rfl
end Formalism.L2.Th1.H
