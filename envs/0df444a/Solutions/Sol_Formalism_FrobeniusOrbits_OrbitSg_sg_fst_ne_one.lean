-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.OrbitSg.sg_fst_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:37:24.348969+00:00
-- url     : https://prove2.me/submissions/98ee1eca-f961-4edf-acd9-b45105abe661

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
theorem _root_.solution (e : ℕ) : (sg e).1 ≠ 1 := by
  simp only [sg]; decide
end Formalism.FrobeniusOrbits.OrbitSg
