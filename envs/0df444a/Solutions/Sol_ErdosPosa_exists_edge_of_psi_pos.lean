-- Prove2me | solution 1 for ErdosPosa.exists_edge_of_psi_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:31:55.379346+00:00
-- url     : https://prove2.me/submissions/1c00d8f4-f7ed-4eb4-a96a-9170f3f50a36

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPShort
public import Definitions.Def_ErdosPosaLib_EPPacking
public import Theorems.Thm_ErdosPosa_restr_adj
attribute [local simp] ErdosPosa.restr_adj



set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
namespace ErdosPosa
theorem _root_.solution [Fintype V] {H : SimpleGraph V} (h : 0 < psi H) :
    ∃ u w, H.Adj u w := by
  by_contra hcon
  push Not at hcon
  have : psi H = 0 := by
    unfold psi
    apply Finset.sum_eq_zero
    intro v _
    have : deg H v = 0 := by
      rw [deg, Set.ncard_eq_zero]
      ext w; simp [hcon v w]
    simp [this, wt]
  omega
end ErdosPosa
