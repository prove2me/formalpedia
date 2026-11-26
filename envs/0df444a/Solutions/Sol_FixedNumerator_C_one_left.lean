-- Prove2me | solution 1 for FixedNumerator.C_one_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:46:06.29525+00:00
-- url     : https://prove2.me/submissions/321d31e0-cdf5-4c2a-87b5-6105836ac441

module
public import Definitions.Def_FixedNumerator_Defs
public import Definitions.Def_FixedNumerator_Primary

set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator
namespace FixedNumerator
theorem _root_.solution (c : GaussianInt) : C 1 c = 0 := by simp [C, Zsqrtd.norm]
end FixedNumerator
