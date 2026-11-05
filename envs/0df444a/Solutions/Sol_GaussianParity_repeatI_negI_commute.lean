-- Prove2me | solution 1 for GaussianParity.repeatI_negI_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.497676+00:00
-- url     : https://prove2.me/submissions/a9d023bd-17d5-4503-9aba-4f6fcb553871

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Theorems.Thm_GaussianParity_mulI_negI
import Theorems.Thm_GaussianParity_negI_mulI

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (q : Nat) (z : GInt) :
    repeatI q (negI z) = negI (repeatI q z) := by
  induction q with
  | zero => rfl
  | succ q ih =>
    simp only [repeatI, ih]
    rw [mulI_negI, negI_mulI]
end GaussianParity
