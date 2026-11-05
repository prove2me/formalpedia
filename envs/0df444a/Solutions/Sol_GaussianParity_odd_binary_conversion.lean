-- Prove2me | solution 1 for GaussianParity.odd_binary_conversion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.497676+00:00
-- url     : https://prove2.me/submissions/45e00f56-2348-47fb-994a-0cee98a693ed

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Theorems.Thm_GaussianParity_scale_mul
import Theorems.Thm_GaussianParity_repeatI_negI_commute
import Theorems.Thm_GaussianParity_repeatI_cancel
import Theorems.Thm_GaussianParity_repeatPi_odd
import Theorems.Thm_GaussianParity_GInt_ext


set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (q : Nat) (z : GInt) :
    repeatPi (2*q+1) (repeatNegI (q+1) (mulPi z)) =
      scale ((2 : Int)^(q+1)) z := by
  rw [repeatPi_odd]
  simp only [repeatNegI]
  rw [repeatI_negI_commute, repeatI_cancel]
  have hp : mulPi (negI (mulPi z)) = scale 2 z := by
    apply GInt.ext <;> simp only [mulPi, negI, scale] <;> omega
  rw [hp, scale_mul]
  simp [Int.pow_succ]
end GaussianParity
