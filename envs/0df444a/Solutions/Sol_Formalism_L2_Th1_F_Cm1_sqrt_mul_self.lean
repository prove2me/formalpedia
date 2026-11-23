-- Prove2me | solution 1 for Formalism.L2.Th1.F.Cm1.sqrt_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:26:03.174878+00:00
-- url     : https://prove2.me/submissions/f9bc0351-0151-4308-b811-f4ce5066458f

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_CMQuasiPeriodConst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_CmAlternatingForm

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
open Formalism.L2.Th1.F.Cm1
namespace Formalism.L2.Th1.F.Cm1
theorem _root_.solution (d : ℕ) : Real.sqrt d * Real.sqrt d = d :=
  Real.mul_self_sqrt (Nat.cast_nonneg d)
end Formalism.L2.Th1.F.Cm1
