-- Prove2me | solution 1 for Formalism.L2.Th1.F.OperatorUThetaLemmas.conj_herm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:28:38.349585+00:00
-- url     : https://prove2.me/submissions/3fd84753-cc7c-4317-890a-3e76d2ea8a0e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaZeroLogDerivative
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_OperatorUComm

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
open Formalism.L2.Th1.F.OperatorUThetaLemmas
namespace Formalism.L2.Th1.F.OperatorUThetaLemmas
theorem _root_.solution (L : PeriodPair) (x y : ℂ) : conj (herm L x y) = herm L y x := by
  simp only [Formalism.L2.Th1.F.herm, map_div₀, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  ring
end Formalism.L2.Th1.F.OperatorUThetaLemmas
