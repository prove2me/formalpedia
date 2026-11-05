-- Prove2me | solution 1 for GaussianParity.odd_ideal_parity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.497676+00:00
-- url     : https://prove2.me/submissions/6b29967a-dc9d-4baa-8ad8-0850891ba47b

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Theorems.Thm_GaussianParity_pi_odd_ideal

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (q : Nat) (z : GInt)
    (h : PiPowerDivisible (2*q+1) z) :
    ∃ w : GInt, scale ((2 : Int)^q) w = z ∧ w.re % 2 = w.im % 2 := by
  exact (pi_odd_ideal q z).mp h
end GaussianParity
