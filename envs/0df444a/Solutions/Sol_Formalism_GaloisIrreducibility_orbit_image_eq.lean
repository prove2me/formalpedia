-- Prove2me | solution 1 for Formalism.GaloisIrreducibility.orbit_image_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:33.709911+00:00
-- url     : https://prove2.me/submissions/66cd8324-0610-4bf0-9c7f-4737c4ba74ed

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_OrbitSubSum
import Theorems.Thm_Formalism_GaloisIrreducibility_orbit_iterate_mem

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
    O.image f = O := by
  apply Finset.Subset.antisymm
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact hO.1 x hx
  · intro y hy
    obtain ⟨n, hn⟩ := hO.2 (f y) (hO.1 y hy) y hy
    rw [← Function.iterate_succ_apply, Function.iterate_succ_apply'] at hn
    exact Finset.mem_image.mpr ⟨f^[n] y, orbit_iterate_mem hO hy n, hn⟩
end Formalism.GaloisIrreducibility
