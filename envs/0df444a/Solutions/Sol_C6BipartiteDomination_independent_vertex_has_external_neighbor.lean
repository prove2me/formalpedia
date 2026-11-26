-- Prove2me | solution 1 for C6BipartiteDomination.independent_vertex_has_external_neighbor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:42:32.269365+00:00
-- url     : https://prove2.me/submissions/24c6f541-4b9e-46eb-a076-3ba44321e433

import Definitions.Def_C6BipartiteDomination_A2
import Definitions.Def_C6BipartiteDomination_A3
import Theorems.Thm_C6BipartiteDomination_neighbor_of_independent_outside

set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {D : Finset V}
    (hD : Independent G D) (hNoIso : HasNoIsolatedVertices G)
    {v : V} (hv : v ∈ D) : ∃ w ∈ (Finset.univ \ D), G.Adj v w := by
  obtain ⟨w, hadj⟩ := hNoIso v
  have hw : w ∉ D := neighbor_of_independent_outside G hD hv hadj
  exact ⟨w, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hw⟩, hadj⟩
end C6BipartiteDomination
