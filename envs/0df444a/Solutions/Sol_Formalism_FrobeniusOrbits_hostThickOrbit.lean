-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.hostThickOrbit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:07.514592+00:00
-- url     : https://prove2.me/submissions/d88c0e11-3371-480b-a851-ec7715b7d089

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickOrbit
import Theorems.Thm_Formalism_FrobeniusOrbits_ThickOrbit_part_one
import Theorems.Thm_Formalism_FrobeniusOrbits_ThickOrbit_part_two

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical
open Formalism Formalism.FrobeniusOrbits
namespace Formalism.FrobeniusOrbits
theorem _root_.solution : HostThickOrbit := by
  intro n L hn _ T hT hR u₀ t h
  exact ⟨fun hord i₀ => ThickOrbit.part_one T hT hR u₀ t h hord i₀,
    fun hord => ThickOrbit.part_two hn T hT u₀ t h hord⟩
end Formalism.FrobeniusOrbits
