-- Prove2me | solution 1 for FixedNumerator.lam3_dvd_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:35:44.191176+00:00
-- url     : https://prove2.me/submissions/e86ef46a-e4fe-4b47-b840-0604a813e640

module
public import Definitions.Def_FixedNumerator_Defs
public import Definitions.Def_FixedNumerator_Primary

set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator
namespace FixedNumerator
theorem _root_.solution : lam3 ∣ (4 : GaussianInt) := ⟨⟨-1, -1⟩, by decide⟩
end FixedNumerator
