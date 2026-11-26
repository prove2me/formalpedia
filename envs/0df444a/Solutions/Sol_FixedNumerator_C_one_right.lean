-- Prove2me | solution 1 for FixedNumerator.C_one_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:40:17.534539+00:00
-- url     : https://prove2.me/submissions/9362a820-4f9c-4b30-a7f9-58ea4f42f2db

module
public import Definitions.Def_FixedNumerator_Defs
public import Definitions.Def_FixedNumerator_Primary

set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator
namespace FixedNumerator
theorem _root_.solution (c : GaussianInt) : C c 1 = 0 := by simp [C, Zsqrtd.norm]
end FixedNumerator
