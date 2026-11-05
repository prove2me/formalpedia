-- Prove2me | solution 1 for GaussianParity.bothOdd_repeatNegI
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.497676+00:00
-- url     : https://prove2.me/submissions/45cbbb08-119a-487b-9e4e-23b288ca7529

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Theorems.Thm_GaussianParity_bothOdd_negI

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (q : Nat) (z : GInt) (h : BothOdd z) :
    BothOdd (repeatNegI q z) := by
  induction q with
  | zero => exact h
  | succ q ih => exact bothOdd_negI _ ih
end GaussianParity
