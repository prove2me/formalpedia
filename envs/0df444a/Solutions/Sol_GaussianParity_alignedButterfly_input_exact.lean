-- Prove2me | solution 1 for GaussianParity.alignedButterfly_input_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.497676+00:00
-- url     : https://prove2.me/submissions/25691f3b-b275-4b78-8d21-829b7f0d074c

import Std
import Definitions.Def_DyadicCertificates
import Theorems.Thm_GaussianParity_raiseTo_sameValue

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (x y : Fraction) :
    SameValue (raiseTo x (commonExponent x y)) x ∧
    SameValue (raiseTo y (commonExponent x y)) y := by
  constructor
  · apply raiseTo_sameValue
    exact Nat.le_max_left _ _
  · apply raiseTo_sameValue
    exact Nat.le_max_right _ _
end GaussianParity
