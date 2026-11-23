-- Prove2me | solution 1 for BDD.denotation_eq_of_denotation_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:22:05.121667+00:00
-- url     : https://prove2.me/submissions/c6e17619-8315-4f69-abfc-5daaf65867ec

import Definitions.Def_Bdd_Reduce
import Definitions.Def_Bdd_Apply
import Definitions.Def_Bdd_Relabel
import Definitions.Def_Bdd_Choice
import Definitions.Def_Bdd_Restrict
import Definitions.Def_Bdd_Evaluate
import Definitions.Def_Bdd_Sim
import Definitions.Def_Bdd_Size
import Definitions.Def_Bdd_Count
import Definitions.Def_Bdd_BDD
import Theorems.Thm_Lift_olift_evaluate
import Theorems.Thm_Lift_olift_olift
import Theorems.Thm_Nary_restrict_const
import Theorems.Thm_Reduce_oreduce_evaluate
import Theorems.Thm_Relabel_orelabel_id
attribute [local simp] Lift.olift_evaluate
attribute [local simp] Lift.olift_olift
attribute [local simp] Nary.restrict_const
attribute [local simp] Reduce.oreduce_evaluate
attribute [local simp] Relabel.orelabel_id


section
set_option autoImplicit true
attribute [local implicit_reducible] OBdd Bdd.Ordered Lift.olift Relabel.orelabel Reduce.oreduce
namespace BDD
attribute [local implicit_reducible] lift
attribute [local implicit_reducible] denotation
private lemma Vector.append_take (v : Vector α n) (u : Vector α m) : (v ++ u).take n = (Vector.cast (by simp) v) := by
  ext i hi
  simp only [Vector.getElem_cast, Vector.getElem_take hi]
  exact Vector.getElem_append_left (by omega)
private lemma denotation_append {B : BDD} {hn : B.nvars ≤ n} {hm : n ≤ m} {J : Vector Bool (m - n)} :
    B.denotation hn I = B.denotation (n := m) (.trans hn hm) (Vector.cast (by omega) (I ++ J)) := by
  rw [denotation_cast]
  swap; omega
  conv =>
    rhs
    rw [denotation_take (m := n) (hn := by omega) (hm1 := hn) (hm2 := by simp)]
  rw [Vector.append_take, denotation_cast]
private lemma denotation_eq_of_denotation_eq_leq (B C : BDD) (hn : max B.nvars C.nvars ≤ n) (hm : max B.nvars C.nvars ≤ m) (hnm : n ≤ m):
    B.denotation (n := n) (by omega) = C.denotation (n := n) (by omega) →
    B.denotation (n := m) (by omega) = C.denotation (n := m) (by omega) := by
  intro h
  ext I
  rw [denotation_take (hm2 := hnm)]
  rw [denotation_take (hm2 := hnm)]
  rw [← denotation_cast (show min n m = n by omega)]
  rw [← denotation_cast (show min n m = n by omega)]
  rw [h]
  all_goals omega
private lemma denotation_eq_of_denotation_eq_geq (B C : BDD) (hn : max B.nvars C.nvars ≤ n) (hm : max B.nvars C.nvars ≤ m) (hnm : n ≤ m):
    B.denotation (n := m) (by omega) = C.denotation (n := m) (by omega) →
    B.denotation (n := n) (by omega) = C.denotation (n := n) (by omega) := by
  intro h
  ext I
  rw [denotation_append (hm := hnm) (J := Vector.replicate _ false)]
  rw [denotation_append (hm := hnm) (J := Vector.replicate _ false)]
  rw [h]
attribute [local implicit_reducible] const var apply
attribute [local implicit_reducible] relabel'' relabel'
attribute [local implicit_reducible] restrict restrict'
end BDD
end

set_option autoImplicit true
attribute [local implicit_reducible] OBdd Bdd.Ordered Lift.olift Relabel.orelabel Reduce.oreduce
open BDD
attribute [local implicit_reducible] lift
attribute [local implicit_reducible] denotation
namespace BDD
theorem _root_.solution {B C : BDD} (hn : B.nvars ⊔ C.nvars ≤ n) (hm : B.nvars ⊔ C.nvars ≤ m) :
    B.denotation (n := n) (by omega) = C.denotation (n := n) (by omega) →
    B.denotation (n := m) (by omega) = C.denotation (n := m) (by omega) := fun h ↦
  if hleq : n ≤ m
  then denotation_eq_of_denotation_eq_leq B C hn hm hleq h
  else denotation_eq_of_denotation_eq_geq _ _ hm hn (le_of_not_ge hleq) h
end BDD
