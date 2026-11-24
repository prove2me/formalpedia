-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.OrbitSg.orderOf_oneNeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:37:23.477583+00:00
-- url     : https://prove2.me/submissions/ab5fc630-fdfa-484a-b242-53e446c5a797

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
theorem _root_.solution : orderOf (((1 : ℤˣ), (-1 : ℤˣ)) : G0) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by decide) (by decide)
end Formalism.FrobeniusOrbits.OrbitSg
