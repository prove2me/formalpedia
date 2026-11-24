-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.OrbitSg.orderOf_negOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:37:10.066797+00:00
-- url     : https://prove2.me/submissions/dc6df9a0-d142-44b6-8dbe-02a51d484c45

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostOrbitCountSg
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrbitSg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.FrobeniusOrbits.OrbitSg
namespace Formalism.FrobeniusOrbits.OrbitSg
theorem _root_.solution : orderOf (-1 : ℤˣ) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by decide) (by decide)
end Formalism.FrobeniusOrbits.OrbitSg
