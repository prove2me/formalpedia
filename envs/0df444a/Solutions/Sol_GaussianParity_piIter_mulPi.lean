-- Prove2me | solution 1 for GaussianParity.piIter_mulPi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.342874+00:00
-- url     : https://prove2.me/submissions/24345628-ae28-47e2-83a2-586af01ea0ea

import Std
import Definitions.Def_DyadicCertificates

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (n : Nat) (z : GInt) :
    piIter n (mulPi z) = mulPi (piIter n z) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [piIter, ih]
end GaussianParity
