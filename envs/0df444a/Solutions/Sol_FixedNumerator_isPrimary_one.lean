-- Prove2me | solution 1 for FixedNumerator.isPrimary_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:40:06.714502+00:00
-- url     : https://prove2.me/submissions/ddd33939-385a-49fc-b4b6-3b17f6947c0e

module
public import Definitions.Def_FixedNumerator_Defs
public import Definitions.Def_FixedNumerator_Primary

set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator
namespace FixedNumerator
theorem _root_.solution : IsPrimary 1 := ⟨0, by simp⟩
end FixedNumerator
