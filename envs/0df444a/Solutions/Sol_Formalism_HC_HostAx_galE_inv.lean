-- Prove2me | solution 1 for Formalism.HC.HostAx.galE_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:03:46.616516+00:00
-- url     : https://prove2.me/submissions/0e7f1cb6-3cff-4113-a42a-b5af70fd76b5

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
theorem _root_.solution (σ : H.E ≃ₐ[ℚ] H.E) : H.galE σ⁻¹ = (H.galE σ)⁻¹ := map_inv H.gal σ
end Formalism.HC.HostAx
