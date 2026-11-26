-- Prove2me | solution 1 for FixedNumerator.C_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:40:10.931952+00:00
-- url     : https://prove2.me/submissions/3944785c-df7c-4934-bb4d-181cdf6bbe5c

module
public import Definitions.Def_FixedNumerator_Defs
public import Definitions.Def_FixedNumerator_Primary

set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator
namespace FixedNumerator
theorem _root_.solution (a c : GaussianInt) : C a c = C c a := by unfold C; ring
end FixedNumerator
