-- Prove2me | solution 1 for Formalism.L2.Th1.E.OperatorUThetaLemmas.opU_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:28:04.842421+00:00
-- url     : https://prove2.me/submissions/af0983ad-70a1-4669-8022-47323d3a3df0

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
theorem _root_.solution (L : PeriodPair) (x a : ℂ) (f : ℂ → ℂ) :
    opU L x (fun z => a * f z) = fun z => a * opU L x f z := by
  funext z
  simp only [opU]
  ring
end Formalism.L2.Th1.E.OperatorUThetaLemmas
