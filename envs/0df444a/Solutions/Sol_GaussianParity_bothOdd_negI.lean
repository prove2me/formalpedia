-- Prove2me | solution 1 for GaussianParity.bothOdd_negI
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.497676+00:00
-- url     : https://prove2.me/submissions/496cd7b4-12c8-4641-880c-9d55a5eedc08

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (z : GInt) (h : BothOdd z) : BothOdd (negI z) := by
  simp only [BothOdd, negI] at *
  omega
end GaussianParity
