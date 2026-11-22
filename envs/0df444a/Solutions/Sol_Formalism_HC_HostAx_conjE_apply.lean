-- Prove2me | solution 1 for Formalism.HC.HostAx.conjE_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:05:39.148433+00:00
-- url     : https://prove2.me/submissions/6d4c073f-6caa-44f2-abde-39291f35267d

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ConjEMemHostFIff
import Theorems.Thm_Formalism_HC_HostAx_galE_conjE

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
theorem _root_.solution (ψ : H.E →+* ℂ) (x : H.E) : ψ (H.conj x) = starRingEnd ℂ (ψ x) := (H.der.conj_iff ψ H.conj).2 H.galE_conjE x
end Formalism.HC.HostAx
