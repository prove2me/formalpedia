-- Prove2me | solution 1 for DeletionCode.WalkSelection.ScanState.generating
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:12.720801+00:00
-- url     : https://prove2.me/submissions/c79331e3-7f64-4350-b84e-06a2eb437d8b

import Definitions.Def_DeletionCode_ClosedWalk
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_DeletionCode_WalkSelection
import Theorems.Thm_DeletionCode_WalkSelection_coordinate_unchanged_before
import Theorems.Thm_DeletionCode_WitnessAlgebra_negative_step_source


set_option autoImplicit true
open DeletionCode DeletionCode.WalkSelection
open scoped BigOperators
variable {V : Type*} [AddCommGroup V] [Module ℚ V] {m : ℕ}
namespace DeletionCode.WalkSelection
namespace ScanState
theorem _root_.solution {H : Type*} {p : Fin (m + 1) → H → ℚ}
    {Good : Finset (Fin m) → Prop} {n : ℕ} {S : Finset (Fin m)}
    (hs : ScanState (walkStep p) Good n S)
    (hp : ∀ j, WitnessAlgebra.BooleanVector (p j)) : GeneratingSelected p S := by
  classical
  intro i hi h hneg
  by_cases hbase : p 0 h = 0
  · right
    by_contra hnone
    have hselected : ∀ r ∈ S, r.val < i.val → walkStep p r h = 0 := by
      intro r hr hri
      by_contra hrzero
      exact hnone ⟨r, hr, hri, hrzero⟩
    have hzero : ∀ j : Fin m, j.val < i.val → walkStep p j h = 0 := by
      intro j hji
      obtain ⟨r, hr, hrj, heq⟩ := hs.covered j (by have := hs.before i hi; omega)
      have hrzero := hselected r hr (by omega)
      rcases heq with heq | heq
      · exact (congrFun heq h).trans hrzero
      · have hcoord := congrFun heq h
        simpa only [Pi.neg_apply, hrzero, neg_zero] using hcoord
    have hsame := coordinate_unchanged_before p i.val (by have := i.isLt; omega) h hzero
    change p i.castSucc h = p 0 h at hsame
    have hpone := WitnessAlgebra.negative_step_source (p i.castSucc) (p i.succ)
      (hp i.castSucc) (hp i.succ) h hneg
    exact zero_ne_one (hbase.symm.trans (hsame.symm.trans hpone))
  · exact Or.inl hbase
end ScanState
end DeletionCode.WalkSelection
