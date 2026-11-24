-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.hostOrbitsFin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:26:18.512936+00:00
-- url     : https://prove2.me/submissions/20037f7e-aa6c-4eee-929d-181db87fbb63

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostOrbitsPlaces
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
import Theorems.Thm_Formalism_FrobeniusOrbits_hostOrbits
import Theorems.Thm_Formalism_FrobeniusOrbits_hostOrbitsPlaces
import Theorems.Thm_Formalism_FrobeniusOrbits_hostOrbitCount
import Theorems.Thm_Formalism_FrobeniusOrbits_hostFiniteOrder

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
theorem _root_.solution : HostOrbits ∧ HostOrbitsPlaces ∧ HostOrbitCount ∧ HostFiniteOrder :=
  ⟨hostOrbits, hostOrbitsPlaces, hostOrbitCount, hostFiniteOrder⟩
end Formalism.FrobeniusOrbits
