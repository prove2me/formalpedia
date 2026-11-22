-- Prove2me | solution 1 for Formalism.LT.LTL.inverseIntegralClasses_cc_s_fact
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:01:16.361687+00:00
-- url     : https://prove2.me/submissions/e4f3836b-c158-4628-acd2-f280f412ec6b

import Definitions.Def_Formalism_TorsionNormIteration_LTLemma
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_LTLemma

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
universe u
open Formalism Formalism.LT Formalism.LT.LTL
open Formalism.G Formalism.G.LogCR Formalism.LT.InvIntP
variable {K : Type u} [NormedField K] {ι : Type*}
namespace Formalism.LT.LTL
theorem _root_.solution (e' : PowerSeries K) (h0 : constantCoeff e' = 0) (i : ι) :
    MvPowerSeries.constantCoeff (e'.subst (MvPowerSeries.X i : MvPowerSeries ι K)) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (by simp) _ h0
end Formalism.LT.LTL
