-- Prove2me | solution 1 for Formalism.G.LogP.psubst_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:09:35.036594+00:00
-- url     : https://prove2.me/submissions/d658e663-254b-4ed1-b241-0f861404908f

import Definitions.Def_Formalism_FormalGroupLog_Statement
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open Formalism Formalism.G Formalism.G.LogP
open Formalism.G.LogCR
variable {R : Type*} [CommRing R]
namespace Formalism.G.LogP
theorem _root_.solution {σ : Type*} {a : MvPowerSeries σ R} (ha : PowerSeries.HasSubst a) :
    (1 : PowerSeries R).subst a = 1 := by
  rw [← PowerSeries.coe_substAlgHom ha, map_one]
end Formalism.G.LogP
