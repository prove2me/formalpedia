-- Prove2me | solution 1 for BDD.denotation_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:24:37.425409+00:00
-- url     : https://prove2.me/submissions/6e55d582-7058-49e8-aa1b-16a9ffcee7a8

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
import Theorems.Thm_BDD_denotation_congr_dependsOn

set_option autoImplicit true
attribute [local implicit_reducible] OBdd Bdd.Ordered Lift.olift Relabel.orelabel Reduce.oreduce
open BDD
attribute [local implicit_reducible] lift
attribute [local implicit_reducible] denotation
namespace BDD
theorem _root_.solution {B : BDD}
    {I : Vector Bool n} {J : Vector Bool m} {hn : B.nvars ≤ n} {hm : B.nvars ≤ m} :
    (∀ i : Fin B.nvars, I[i] = J[i]) → B.denotation hn I = B.denotation hm J := by
  grind only [denotation_congr_dependsOn]
end BDD
