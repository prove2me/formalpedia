-- Prove2me | solution 1 for BondySimonovits.dist_le_of_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:03:41.955803+00:00
-- url     : https://prove2.me/submissions/d06162b5-9b64-4c76-802f-3d6e3715e625

module
public import Definitions.Def_BondySimonovitsLib_BSBasic
public import Definitions.Def_BondySimonovitsLib_BSLayers

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits
variable {V : Type*} (K : SimpleGraph V)
namespace BondySimonovits
theorem _root_.solution {x u v : V} (hr : K.Reachable x u) (h : K.Adj u v) :
    K.dist x v ≤ K.dist x u + 1 := by
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  have := SimpleGraph.dist_le (p.concat h)
  simpa [hp] using this
end BondySimonovits
