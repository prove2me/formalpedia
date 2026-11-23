-- Prove2me | solution 1 for Formalism.HC.HostAx.isConj_iff_galE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:27.263838+00:00
-- url     : https://prove2.me/submissions/958aa6bd-c8ff-467b-a65b-d18344d80567

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
theorem _root_.solution (ψ : H.E →+* ℂ) (σ : H.E ≃ₐ[ℚ] H.E) :
    (∀ x, ψ (σ x) = starRingEnd ℂ (ψ x)) ↔ H.galE σ = φ.cc := H.der.conj_iff ψ σ
end Formalism.HC.HostAx
