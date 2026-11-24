-- Prove2me | solution 1 for BondySimonovits.parent_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:09:10.977926+00:00
-- url     : https://prove2.me/submissions/ffc5961e-3be6-47b5-be1a-b837379f7b6d

module
public import Definitions.Def_BondySimonovitsLib_BSBasic
public import Definitions.Def_BondySimonovitsLib_BSLayers
public import Theorems.Thm_BondySimonovits_dist_le_of_adj

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits
variable {V : Type*} (K : SimpleGraph V)
namespace BondySimonovits
theorem _root_.solution {x v : V} (hr : K.Reachable x v) (hpos : 0 < K.dist x v) :
    ∃ w, K.Adj v w ∧ K.dist x w + 1 = K.dist x v := by
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  have hne : v ≠ x := by
    rintro rfl
    simp at hpos
  obtain ⟨w, h, q, hq⟩ := Walk.exists_eq_cons_of_ne hne p.reverse
  have hlen : q.length + 1 = K.dist x v := by
    have h' := congrArg Walk.length hq
    rw [Walk.length_reverse, Walk.length_cons] at h'
    omega
  have hxw : K.Reachable x w := ⟨q.reverse⟩
  have b1 : K.dist x w ≤ q.length := by
    have := SimpleGraph.dist_le q.reverse
    simpa using this
  have b2 := dist_le_of_adj K hxw h.symm
  exact ⟨w, h, by omega⟩
end BondySimonovits
