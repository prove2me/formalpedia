-- Prove2me | solution 1 for Formalism.LT.InvIntP.low_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:00:10.393542+00:00
-- url     : https://prove2.me/submissions/9f500d4a-fe80-40b5-8002-968769c2e347

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u v
open Formalism Formalism.LT Formalism.LT.InvIntP
open Formalism.G Formalism.G.LogCR
variable {K : Type u} [NormedField K] {ι : Type v}
namespace Formalism.LT.InvIntP
theorem _root_.solution {x : MvPowerSeries ι K} (hx : MvPowerSeries.constantCoeff x = 0) : Low 1 x := by
  intro d hd
  have h0 : d = 0 := (Finsupp.degree_eq_zero_iff d).1 (by omega)
  subst h0
  rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hx]
end Formalism.LT.InvIntP
