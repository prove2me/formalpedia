-- Prove2me | solution 1 for GaussianParity.repeatNegI_residue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.497676+00:00
-- url     : https://prove2.me/submissions/5936b2eb-a361-4edb-91e3-4b10b86cb27c

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Theorems.Thm_GaussianParity_residue_negI

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (q : Nat) (z : GInt) :
    residue (repeatNegI q z) = residue z := by
  induction q with
  | zero => rfl
  | succ q ih => simp [repeatNegI, residue_negI, ih]
end GaussianParity
