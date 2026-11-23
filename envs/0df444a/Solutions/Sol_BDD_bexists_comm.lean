-- Prove2me | solution 1 for BDD.bexists_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:22:17.404576+00:00
-- url     : https://prove2.me/submissions/f241ff8f-3c5d-405f-8acf-682232a5b2c3

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
    ((B.bexists i).bexists j).denotation h I = ((B.bexists j).bexists i).denotation (by simp_all) I := by
  repeat
    ( rw [bexists_denotation (i := i.1) (hi := by simp_all; omega)]
      rw [bexists_denotation (i := j.1) (hi := by simp_all; omega)]
      simp only [Bool.exists_bool, Bool.decide_or, Bool.decide_eq_true]
    )
  cases decEq j.1 i.1 with
  | isTrue ht => simp_rw [ht]
  | isFalse hf =>
    rw [show ((I.set (↑j) false _).set (↑i) false _) = _ by refine Vector.set_comm _ _ hf]
    rw [show ((I.set (↑j) false _).set (↑i) true  _) = _ by refine Vector.set_comm _ _ hf]
    rw [show ((I.set (↑j) true  _).set (↑i) false _) = _ by refine Vector.set_comm _ _ hf]
    rw [show ((I.set (↑j) true  _).set (↑i) true  _) = _ by refine Vector.set_comm _ _ hf]
    rw [Bool.or_assoc]
    rw [Bool.or_assoc]
    congr 1
    conv =>
      rhs
      rw [Bool.or_comm]
      rw [Bool.or_assoc]
    congr 1
    rw [Bool.or_comm]
end BDD
