-- Prove2me | solution 1 for Formalism.HC.HostAx.galE_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:30:17.175188+00:00
-- url     : https://prove2.me/submissions/958410a0-e9f3-49c9-b28d-367985e07552

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
theorem _root_.solution (σ : H.E ≃ₐ[ℚ] H.E) (k : ℕ) : H.galE (σ ^ k) = H.galE σ ^ k := map_pow H.gal σ k
end Formalism.HC.HostAx
