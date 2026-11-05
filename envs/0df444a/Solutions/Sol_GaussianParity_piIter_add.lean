-- Prove2me | solution 1 for GaussianParity.piIter_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.342874+00:00
-- url     : https://prove2.me/submissions/1a3dd765-b8fb-4837-905f-0bf54c20baeb

import Std
import Definitions.Def_DyadicCertificates

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (n m : Nat) (z : GInt) :
    piIter (n + m) z = piIter n (piIter m z) := by
  induction n with
  | zero => simp only [Nat.zero_add, piIter]
  | succ n ih => simp only [Nat.succ_add, piIter, ih]
end GaussianParity
