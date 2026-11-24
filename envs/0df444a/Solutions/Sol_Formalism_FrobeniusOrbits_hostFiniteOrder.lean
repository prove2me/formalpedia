-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.hostFiniteOrder
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:03:24.498976+00:00
-- url     : https://prove2.me/submissions/40905be4-4979-4c33-9b53-2864dbac794b

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostOrbitsPlaces
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
import Theorems.Thm_Formalism_FrobeniusOrbits_Orbits_dim_bound
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_finrank_cmField


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Orbits
namespace Formalism.FrobeniusOrbits
theorem _root_.solution : HostFiniteOrder := by
  unfold HostFiniteOrder
  intro e q d hqd L _ _ ζ a b h k g hg M hM hne
  have := dim_bound k g hg M hM hne
  rwa [Galois.finrank_cmField hqd h] at this
end Formalism.FrobeniusOrbits
