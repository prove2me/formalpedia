-- Prove2me | solution 1 for BDD.find_none
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:21:43.934929+00:00
-- url     : https://prove2.me/submissions/167c849f-9cf2-40e0-bb60-b1e86b479744

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
namespace BDD
theorem _root_.solution {B : BDD} : B.find.isNone → B.denotation' = Function.const _ false := by
  intro h
  ext I
  simp only [find] at h
  split at h
  next ht =>
    simp +instances only [SemanticEquiv, const_nvars, const_denotation] at ht
    rw [funext_iff] at ht
    simp only [denotation']
    have := ht (Vector.cast (by simp) I)
    simp only [le_refl, denotation_cast, Function.const_apply] at this
    simpa
  next hf => contradiction
end BDD
