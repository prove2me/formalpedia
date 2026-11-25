-- Prove2me | solution 1 for ErdosPosa.psi_deleteEdge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:33:49.522508+00:00
-- url     : https://prove2.me/submissions/f198c784-ce95-42e5-90c0-2adff5fa0bb1

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPShort
public import Definitions.Def_ErdosPosaLib_EPPacking
public import Theorems.Thm_ErdosPosa_wt_pred
public import Theorems.Thm_ErdosPosa_deg_deleteEdge_left
public import Theorems.Thm_ErdosPosa_deg_deleteEdge_right
public import Theorems.Thm_ErdosPosa_deg_deleteEdge_other
public import Theorems.Thm_ErdosPosa_deg_pos_of_adj
public import Theorems.Thm_ErdosPosa_restr_adj
attribute [local simp] ErdosPosa.restr_adj



set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
variable [Finite V] {H : SimpleGraph V} {y z : V}
variable [Fintype V]
namespace ErdosPosa
theorem _root_.solution (hyz : H.Adj y z) : psi H - 2 ≤ psi (H.deleteEdges {s(y, z)}) := by
  classical
  have key : ∀ v, wt (deg H v) ≤ wt (deg (H.deleteEdges {s(y, z)}) v) +
      ((if v = y then 1 else 0) + (if v = z then 1 else 0)) := by
    intro v
    by_cases hvy : v = y
    · subst hvy
      have hz : v ≠ z := hyz.ne
      rw [deg_deleteEdge_left hyz]
      simp only [↓reduceIte, hz]
      have := wt_pred (deg H v) (deg_pos_of_adj hyz)
      linarith
    by_cases hvz : v = z
    · subst hvz
      rw [deg_deleteEdge_right hyz]
      simp only [↓reduceIte, hvy]
      have := wt_pred (deg H v) (deg_pos_of_adj hyz.symm)
      linarith
    rw [deg_deleteEdge_other v hvy hvz]
    simp [hvy, hvz]
  have := Finset.sum_le_sum (s := Finset.univ) (fun v _ => key v)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
    at this
  simp only [Finset.mem_univ, ↓reduceIte] at this
  unfold psi
  linarith
end ErdosPosa
