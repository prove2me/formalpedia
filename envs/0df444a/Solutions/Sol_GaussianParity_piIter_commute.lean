-- Prove2me | solution 1 for GaussianParity.piIter_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.342874+00:00
-- url     : https://prove2.me/submissions/81dbb1b7-8c11-4b3d-bcb2-9b5bf33f0d02

import Std
import Definitions.Def_DyadicCertificates
import Theorems.Thm_GaussianParity_piIter_add

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (n m : Nat) (z : GInt) :
    piIter n (piIter m z) = piIter m (piIter n z) := by
  rw [← piIter_add, ← piIter_add, Nat.add_comm]
end GaussianParity
