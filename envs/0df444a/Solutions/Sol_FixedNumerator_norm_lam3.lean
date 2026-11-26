-- Prove2me | solution 1 for FixedNumerator.norm_lam3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:41:23.096557+00:00
-- url     : https://prove2.me/submissions/c95cfbe1-c1ef-4361-b524-919cd8430092

module
public import Definitions.Def_FixedNumerator_Local
public import Definitions.Def_FixedNumerator_Split

set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator
namespace FixedNumerator
theorem _root_.solution : lam3.norm = 8 := by simp [lam3, Zsqrtd.norm]
end FixedNumerator
