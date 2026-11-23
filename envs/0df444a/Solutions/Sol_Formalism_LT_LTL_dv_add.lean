-- Prove2me | solution 1 for Formalism.LT.LTL.dv_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:41:15.695226+00:00
-- url     : https://prove2.me/submissions/24535c86-a139-430d-a318-2619d355110a

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
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type*}
namespace Formalism.LT.LTL
theorem _root_.solution {c : K} {A B : MvPowerSeries ι K} (hA : DivByMv c A) (hB : DivByMv c B) :
    DivByMv c (A + B) := fun d => by
  rw [map_add]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hA d) (hB d))
end Formalism.LT.LTL
