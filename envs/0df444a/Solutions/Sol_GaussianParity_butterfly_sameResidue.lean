-- Prove2me | solution 1 for GaussianParity.butterfly_sameResidue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.342874+00:00
-- url     : https://prove2.me/submissions/fee7e631-1875-4903-8a0d-2714761c54ca

import Std
import Definitions.Def_DyadicCertificates

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (u v : GInt) (h : SameResidue u v) :
    SameResidue (butterfly u v).1 (butterfly u v).2 := by
  simp only [SameResidue, residue, butterfly, dividePi, numeratorLeft,
    numeratorRight, add, mulI] at *
  omega
end GaussianParity
