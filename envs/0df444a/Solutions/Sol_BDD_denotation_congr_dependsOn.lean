-- Prove2me | solution 1 for BDD.denotation_congr_dependsOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:22:37.413128+00:00
-- url     : https://prove2.me/submissions/acd5503f-c131-4d4a-8ed5-6d1f141d7927

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
import Theorems.Thm_Nary_eq_of_forall_dependency_getElem_eq


set_option autoImplicit true
attribute [local implicit_reducible] OBdd Bdd.Ordered Lift.olift Relabel.orelabel Reduce.oreduce
open BDD
attribute [local implicit_reducible] lift
attribute [local implicit_reducible] denotation
namespace BDD
theorem _root_.solution {B : BDD}
    {I : Vector Bool n} {J : Vector Bool m} {hn : B.nvars ≤ n} {hm : B.nvars ≤ m} :
    (∀ i : Nary.Dependency B.denotation', I[i.val] = J[i.val]) →
    B.denotation hn I = B.denotation hm J := by
  intro h1
  have h2 : min B.nvars n = B.nvars := by omega
  have h3 : min B.nvars m = B.nvars := by omega
  suffices B.denotation' ((I.take B.nvars).cast h2) = B.denotation' ((J.take B.nvars).cast h3) by
    grind only [denotation_cast, !denotation_take]
  apply Nary.eq_of_forall_dependency_getElem_eq
  rintro ⟨j, h4⟩
  calc
  (I.take B.nvars)[↑j]
  _ = I[j] := by
    grind only [= Fin.getElem_fin, = Vector.getElem_take]
  _ = J[j] := by exact h1 ⟨j, h4⟩
  _ = (J.take B.nvars)[↑j] := by
    grind only [= Fin.getElem_fin, = Vector.getElem_take]
end BDD
