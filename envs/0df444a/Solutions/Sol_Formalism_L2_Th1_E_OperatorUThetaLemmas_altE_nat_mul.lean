-- Prove2me | solution 1 for Formalism.L2.Th1.E.OperatorUThetaLemmas.altE_nat_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:24:04.114542+00:00
-- url     : https://prove2.me/submissions/257621eb-bb84-43c8-b2cb-91f9f2a484f5

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_OpUTh0RootOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Formalism.L2.Th1.E.OperatorUThetaLemmas
open Formalism.L2.Th1.F
namespace Formalism.L2.Th1.E.OperatorUThetaLemmas
theorem _root_.solution (L : PeriodPair) (N : ℕ) (x y : ℂ) :
    altE L ((N : ℂ) * x) ((N : ℂ) * y) = (N : ℝ) ^ 2 * altE L x y := by
  have h : herm L ((N : ℂ) * x) ((N : ℂ) * y) = (((N : ℝ) ^ 2 : ℝ) : ℂ) * herm L x y := by
    simp only [herm, map_mul, Complex.conj_natCast]
    push_cast
    ring
  simp only [altE, h, Complex.im_ofReal_mul]
end Formalism.L2.Th1.E.OperatorUThetaLemmas
