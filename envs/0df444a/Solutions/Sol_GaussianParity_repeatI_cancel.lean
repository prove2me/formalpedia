-- Prove2me | solution 1 for GaussianParity.repeatI_cancel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.497676+00:00
-- url     : https://prove2.me/submissions/47217598-d465-431e-ba05-ced00940f40e

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Theorems.Thm_GaussianParity_mulI_negI
import Theorems.Thm_GaussianParity_repeatI_negI_commute

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (q : Nat) (z : GInt) :
    repeatI q (repeatNegI q z) = z := by
  induction q with
  | zero => rfl
  | succ q ih =>
    simp only [repeatNegI, repeatI]
    rw [repeatI_negI_commute, mulI_negI, ih]
end GaussianParity
