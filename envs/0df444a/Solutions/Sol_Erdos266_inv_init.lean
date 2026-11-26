-- Prove2me | solution 1 for Erdos266.inv_init
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:04:07.524133+00:00
-- url     : https://prove2.me/submissions/9dfe5d10-35f8-4998-9fc0-ff7899adce44

module
public import Definitions.Def_Erdos266_Algorithm
public import Definitions.Def_Erdos266_Recursion
public import Theorems.Thm_Erdos266_dOf_lt_two
public import Theorems.Thm_Erdos266_dOf_two

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution : Inv 2 initSt := by
  refine ⟨le_rfl, ?_, ?_⟩
  · intro l hl j hj
    rw [dOf_lt_two hl] at hj
    omega
  · intro i hi
    rw [dOf_two] at hi
    omega
end Erdos266
