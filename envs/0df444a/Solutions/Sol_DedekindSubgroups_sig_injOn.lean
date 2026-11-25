-- Prove2me | solution 1 for DedekindSubgroups.sig_injOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:05:36.578797+00:00
-- url     : https://prove2.me/submissions/a7058111-19d2-410e-9be0-5fc855f0fcc0

module
public import Definitions.Def_DedekindSubgroups_Meyer
public import Definitions.Def_DedekindSubgroups_Parity

set_option autoImplicit true
@[expose] public section
public section
open Finset Equiv
open DedekindSubgroups
variable {h h' k : ℕ}
namespace DedekindSubgroups
theorem _root_.solution (hinv : h * h' % k = 1) {x y : ℕ} (hx : x < k) (hy : y < k)
    (he : sig h k x = sig h k y) : x = y := by
  rw [← sig_sig hinv hx, ← sig_sig hinv hy, he]
end DedekindSubgroups
