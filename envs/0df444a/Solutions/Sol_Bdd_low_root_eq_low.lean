-- Prove2me | solution 1 for Bdd.low_root_eq_low
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:58:40.427174+00:00
-- url     : https://prove2.me/submissions/93bed415-31f4-4924-b477-a8574612ea91

import Mathlib.Data.Fintype.Sum
import Init.Data.ToString.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic.Linarith
import Definitions.Def_Bdd_Nary
import Definitions.Def_Bdd_DecisionTree
import Definitions.Def_Bdd_Basic

set_option autoImplicit true
open Pointer
open Bdd
attribute [local instance_reducible] OBdd Bdd.Ordered
namespace Bdd
theorem _root_.solution {B : Bdd n m} {h : B.root = node j} : (B.low h).root = B.heap[j].low := rfl
end Bdd
