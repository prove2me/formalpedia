-- Prove2me | solution 1 for GaussianParity.repeatPi_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.497676+00:00
-- url     : https://prove2.me/submissions/55fd06cf-73d9-4a6f-86db-a9be55ad5c22

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Theorems.Thm_GaussianParity_repeatPi_even
import Theorems.Thm_GaussianParity_mulPi_scale

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (q : Nat) (z : GInt) :
    repeatPi (2*q+1) z = scale ((2 : Int)^q) (mulPi (repeatI q z)) := by
  simp only [repeatPi]
  rw [repeatPi_even, mulPi_scale]
end GaussianParity
