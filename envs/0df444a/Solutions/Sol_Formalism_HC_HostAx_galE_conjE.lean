-- Prove2me | solution 1 for Formalism.HC.HostAx.galE_conjE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:03:20.379436+00:00
-- url     : https://prove2.me/submissions/53e905fe-bca9-4f82-b87e-5c8cd2eed17b

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ConjEMemHostFIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC
open Formalism.FrobeniusOrbits
attribute [instance] HostRaw.instField HostRaw.instNF
open Formalism.HC.HostAx
variable {φ : Frame} (H : HostAx φ)
namespace Formalism.HC.HostAx
theorem _root_.solution : H.galE H.conj = φ.cc := H.gal.apply_symm_apply φ.cc
end Formalism.HC.HostAx
