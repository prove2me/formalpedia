-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Orbits.chD_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:15:46.288805+00:00
-- url     : https://prove2.me/submissions/a684c1e5-423a-48c2-9f21-6c8c8843105b

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostOrbitsPlaces
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits

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
open Formalism.FrobeniusOrbits.Orbits
namespace Formalism.FrobeniusOrbits.Orbits
theorem _root_.solution (e : ℕ) (g : GG e) : chD e g = g.1.2 := rfl
end Formalism.FrobeniusOrbits.Orbits
