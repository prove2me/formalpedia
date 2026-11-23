-- Prove2me | solution 1 for BDD.count_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:22:20.812799+00:00
-- url     : https://prove2.me/submissions/e3327f3b-7e6f-4987-a5a2-9b99d7d2fe2e

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
import Theorems.Thm_Count_count_corrent
import Theorems.Thm_Evaluate_evaluate_evaluate
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
theorem _root_.solution {B : BDD} : B.count = Fintype.card { I // B.denotation' I = true } := by
  simp [count, denotation', denotation, lift, Evaluate.evaluate_evaluate, Count.count_corrent, Count.numSolutions, Count.Solution]
end BDD
