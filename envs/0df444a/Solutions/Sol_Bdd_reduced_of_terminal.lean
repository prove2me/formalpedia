-- Prove2me | solution 1 for Bdd.reduced_of_terminal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:00:30.267805+00:00
-- url     : https://prove2.me/submissions/913852d2-336d-4dba-bcd8-01259ebd0d44

import Mathlib.Data.Fintype.Sum
import Init.Data.ToString.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic.Linarith
import Definitions.Def_Bdd_Nary
import Definitions.Def_Bdd_DecisionTree
import Definitions.Def_Bdd_Basic
import Theorems.Thm_OBdd_reduced_of_terminal

set_option autoImplicit true
open Pointer
open Bdd
attribute [local instance_reducible] OBdd Bdd.Ordered
namespace Bdd
theorem _root_.solution : OBdd.Reduced ⟨⟨M, terminal b⟩, o⟩ := OBdd.reduced_of_terminal ⟨b, rfl⟩
end Bdd
