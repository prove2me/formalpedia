-- Prove2me | solution 1 for GaussianParity.even_binary_conversion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.497676+00:00
-- url     : https://prove2.me/submissions/5b13a134-23a3-41f4-a3cc-656f0ade27a0

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Theorems.Thm_GaussianParity_repeatPi_even
import Theorems.Thm_GaussianParity_repeatI_cancel

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (q : Nat) (z : GInt) :
    repeatPi (2*q) (repeatNegI q z) = scale ((2 : Int)^q) z := by
  rw [repeatPi_even, repeatI_cancel]
end GaussianParity
