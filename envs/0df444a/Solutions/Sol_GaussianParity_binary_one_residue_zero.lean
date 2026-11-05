-- Prove2me | solution 1 for GaussianParity.binary_one_residue_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.497676+00:00
-- url     : https://prove2.me/submissions/c4e7fc5b-c54e-4fee-81e1-0d85e10f49bb

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (z : GInt) (h : BinaryDivisible 1 z) :
    residue z = 0 := by
  rcases h with ⟨w, rfl⟩
  simp only [residue, scale]
  omega
end GaussianParity
