-- Prove2me | solution 1 for FairSelling.fin3_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:17:49.845551+00:00
-- url     : https://prove2.me/submissions/6c44eb48-df1c-4dd5-9321-fd38f3c78685

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Definitions.Def_RequestProject_MMSPartition
import Definitions.Def_RequestProject_ThreeAgents
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.restrictVal_mem

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
omit [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (i : Fin 3) :
    i = a ∨ i = b ∨ i = c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases i <;> simp_all
end FairSelling
