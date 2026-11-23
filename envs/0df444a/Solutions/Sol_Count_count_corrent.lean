-- Prove2me | solution 1 for Count.count_corrent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:09:18.607014+00:00
-- url     : https://prove2.me/submissions/a2ae43e3-d065-494a-9889-4028c3619442

import Definitions.Def_Bdd_Basic
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Fintype.BigOperators
import Std.Data.HashMap.Lemmas
import Definitions.Def_Bdd_Count
import Theorems.Thm_Nary_restrict_const
attribute [local simp] Nary.restrict_const



set_option autoImplicit true
attribute [local implicit_reducible] OBdd Bdd.Ordered
open Count
namespace Count
theorem _root_.solution {O : OBdd n m} : count O = numSolutions O := by
  simp only [count]
  split
  next _ inv hin _ _ => exact (inv _ hin).2
end Count
