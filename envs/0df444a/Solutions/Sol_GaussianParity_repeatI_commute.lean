-- Prove2me | solution 1 for GaussianParity.repeatI_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.497676+00:00
-- url     : https://prove2.me/submissions/d9c5c9c7-e682-4b40-b197-51572436a021

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (q : Nat) (z : GInt) :
    repeatI q (mulI z) = mulI (repeatI q z) := by
  induction q with
  | zero => rfl
  | succ q ih => simp [repeatI, ih]
end GaussianParity
