-- Prove2me | solution 1 for Formalism.GaloisIrreducibility.orbit_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:58:43.249211+00:00
-- url     : https://prove2.me/submissions/01ea8dee-0e2b-480b-ae43-fadd975150dc

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_OrbitSubSum

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
theorem _root_.solution {α : Type} {f : α → α} {O : Finset α} (hO : IsOrbit f O) {M' : Multiset α}
    (hM : M'.map f = M') {x : α} (hxO : x ∈ O) (hxM : x ∈ M') : O.val ≤ M' := by
  rw [Multiset.le_iff_subset O.nodup]
  intro y hy
  obtain ⟨n, rfl⟩ := hO.2 x hxO y (Finset.mem_val.mp hy)
  clear hy
  induction n with
  | zero => simpa using hxM
  | succ n ih =>
    rw [Function.iterate_succ_apply', ← hM]
    exact Multiset.mem_map_of_mem f ih
end Formalism.GaloisIrreducibility
