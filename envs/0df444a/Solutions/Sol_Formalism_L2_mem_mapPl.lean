-- Prove2me | solution 1 for Formalism.L2.mem_mapPl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:27:17.725489+00:00
-- url     : https://prove2.me/submissions/3c4c7eb7-062a-4cb9-b354-85e4f344d6e8

import Definitions.Def_Formalism_ConjugateSelfDual_StatementRest
import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_PlaceMapInjectivity_MapPlInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Polynomial Filter
open Formalism Formalism.L2
namespace Formalism.L2
theorem _root_.solution {F L : Type} [Field F] [Field L] (j : F ≃+* L) (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F) :
    RingOfIntegers.mapRingEquiv j x ∈ (mapPl j v).asIdeal ↔ x ∈ v.asIdeal := by
  show (RingOfIntegers.mapRingEquiv j).symm (RingOfIntegers.mapRingEquiv j x) ∈ v.asIdeal ↔ _
  rw [RingEquiv.symm_apply_apply]
end Formalism.L2
