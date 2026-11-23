-- Prove2me | solution 1 for BDD.bforall_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:21:44.873931+00:00
-- url     : https://prove2.me/submissions/210aa967-b888-4bf0-9f8f-24ed50b56a21

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



set_option autoImplicit true
attribute [local implicit_reducible] OBdd Bdd.Ordered Lift.olift Relabel.orelabel Reduce.oreduce
open BDD
attribute [local implicit_reducible] lift
attribute [local implicit_reducible] denotation
attribute [local implicit_reducible] const var apply
attribute [local implicit_reducible] relabel'' relabel'
attribute [local implicit_reducible] restrict restrict'
namespace BDD
theorem _root_.solution {B : BDD} {i j : Fin B.nvars} {I : Vector Bool n} {h} :
    ((B.bforall i).bforall j).denotation h I = ((B.bforall j).bforall i).denotation (by simp_all) I := by
  repeat
    ( rw [bforall_denotation (i := i.1) (hi := by simp_all; omega)]
      rw [bforall_denotation (i := j.1) (hi := by simp_all; omega)]
      simp only [Bool.forall_bool, Bool.decide_and, Bool.decide_eq_true]
    )
  cases decEq j.1 i.1 with
  | isTrue ht => simp_rw [ht]
  | isFalse hf =>
    rw [show ((I.set (↑j) false _).set (↑i) false _) = _ by refine Vector.set_comm _ _ hf]
    rw [show ((I.set (↑j) false _).set (↑i) true  _) = _ by refine Vector.set_comm _ _ hf]
    rw [show ((I.set (↑j) true  _).set (↑i) false _) = _ by refine Vector.set_comm _ _ hf]
    rw [show ((I.set (↑j) true  _).set (↑i) true  _) = _ by refine Vector.set_comm _ _ hf]
    rw [Bool.and_assoc]
    rw [Bool.and_assoc]
    congr 1
    conv =>
      rhs
      rw [Bool.and_comm]
      rw [Bool.and_assoc]
    congr 1
    rw [Bool.and_comm]
end BDD
