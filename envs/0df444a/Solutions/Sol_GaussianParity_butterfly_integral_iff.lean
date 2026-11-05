-- Prove2me | solution 1 for GaussianParity.butterfly_integral_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.342874+00:00
-- url     : https://prove2.me/submissions/2ed32462-1cbe-44bf-96ea-23512cd2d2d7

import Std
import Definitions.Def_DyadicCertificates

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (u v : GInt) :
    PiDvd (numeratorLeft u v) ∧ PiDvd (numeratorRight u v) ↔ SameResidue u v := by
  simp only [PiDvd, numeratorLeft, numeratorRight, add, mulI, SameResidue, residue]
  omega
end GaussianParity
