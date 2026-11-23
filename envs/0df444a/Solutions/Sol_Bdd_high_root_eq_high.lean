-- Prove2me | solution 1 for Bdd.high_root_eq_high
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:58:44.911899+00:00
-- url     : https://prove2.me/submissions/65fa933c-6302-4fe4-ad1e-968e4630889a

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
theorem _root_.solution {B : Bdd n m} {h : B.root = node j} : (B.high h).root = B.heap[j].high := rfl
end Bdd
