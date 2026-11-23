-- Prove2me | solution 1 for BDD.SemanticEquiv.equivalence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:24:39.095738+00:00
-- url     : https://prove2.me/submissions/81126f07-5d2d-4cc3-9d2e-b858dbba8a17

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
import Theorems.Thm_BDD_denotation_eq_of_denotation_eq
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
namespace BDD
namespace SemanticEquiv
theorem _root_.solution : Equivalence SemanticEquiv :=
  { refl := fun _ ↦ rfl,
    symm := fun h ↦ Eq.symm (denotation_eq_of_denotation_eq (by omega) (by omega) h),
    trans := by
      intro B C D hBC hCD
      simp_all only [SemanticEquiv]
      let m := max (max B.nvars C.nvars) D.nvars
      apply denotation_eq_of_denotation_eq (n := m) (by omega) (by omega)
      trans C.denotation (by omega)
      · exact denotation_eq_of_denotation_eq .refl (by omega) hBC
      · exact denotation_eq_of_denotation_eq .refl (by omega) hCD
  }
end SemanticEquiv
end BDD
