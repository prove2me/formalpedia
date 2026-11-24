-- Prove2me | solution 1 for Formalism.L2.Th1.F.ThetaZeroHermitianLemmas.herm_sub_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:37:48.14392+00:00
-- url     : https://prove2.me/submissions/4f11b6f7-f71a-4736-83d5-47e1d02e8e1c

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaZeroLogDerivative
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HermHalfRight
import Theorems.Thm_Formalism_L2_Th1_F_ThetaZeroHermitianLemmas_herm_conj

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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.ThetaZeroHermitianLemmas
namespace Formalism.L2.Th1.F.ThetaZeroHermitianLemmas
theorem _root_.solution (L : PeriodPair) (x y : ℂ) :
    herm L x y - herm L y x = -(2 * Complex.I * (altE L y x : ℂ)) := by
  rw [herm_conj L x y]
  apply Complex.ext <;> simp [altE]
  all_goals ring
end Formalism.L2.Th1.F.ThetaZeroHermitianLemmas
