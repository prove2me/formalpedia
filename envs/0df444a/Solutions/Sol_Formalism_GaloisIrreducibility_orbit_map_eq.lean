-- Prove2me | solution 1 for Formalism.GaloisIrreducibility.orbit_map_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:04:24.558497+00:00
-- url     : https://prove2.me/submissions/4a9b49ed-0513-411a-b474-c607894eba3d

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_OrbitSubSum
import Theorems.Thm_Formalism_GaloisIrreducibility_orbit_image_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GaloisIrreducibility
open Classical
namespace Formalism.GaloisIrreducibility
theorem _root_.solution {α : Type} {f : α → α} {O : Finset α} (hO : IsOrbit f O) :
    O.val.map f = O.val := by
  have hinj : Set.InjOn f O := by
    rw [← Finset.card_image_iff, orbit_image_eq hO]
  rw [← Finset.image_val_of_injOn hinj, orbit_image_eq hO]
end Formalism.GaloisIrreducibility
