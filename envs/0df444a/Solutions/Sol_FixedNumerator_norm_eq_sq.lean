-- Prove2me | solution 1 for FixedNumerator.norm_eq_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:40:56.612278+00:00
-- url     : https://prove2.me/submissions/48a025f5-b39a-4559-a02f-461f37f96488

module
public import Definitions.Def_FixedNumerator_Local
public import Definitions.Def_FixedNumerator_Split

set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator
namespace FixedNumerator
theorem _root_.solution (c : GaussianInt) : c.norm = c.re * c.re + c.im * c.im := by
  simp [Zsqrtd.norm]
end FixedNumerator
