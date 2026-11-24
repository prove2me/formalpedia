-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Orbits.orderOf_conjugation_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:15:47.681827+00:00
-- url     : https://prove2.me/submissions/c3a4f140-8ca6-434c-8ce5-c5c7ea0db244

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
theorem _root_.solution : orderOf c0 = 2 := by
  unfold c0
  apply orderOf_eq_prime
  · ext <;> simp
  · intro h
    have := congrArg Prod.fst h
    simp at this
end Formalism.FrobeniusOrbits.Orbits
