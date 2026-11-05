-- Prove2me | solution 1 for GaussianParity.SameValue.trans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.342874+00:00
-- url     : https://prove2.me/submissions/1a106fcd-f815-46b8-b0c9-e23fc1d7bc27

import Std
import Definitions.Def_DyadicCertificates
import Theorems.Thm_GaussianParity_piIter_commute
import Theorems.Thm_GaussianParity_piIter_injective

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
namespace SameValue
theorem _root_.solution {x y z : Fraction} (hxy : SameValue x y) (hyz : SameValue y z) :
    SameValue x z := by
  unfold SameValue at *
  apply piIter_injective y.exponent
  calc
    piIter y.exponent (piIter z.exponent x.numerator)
        = piIter z.exponent (piIter y.exponent x.numerator) := piIter_commute _ _ _
    _ = piIter z.exponent (piIter x.exponent y.numerator) := congrArg (piIter z.exponent) hxy
    _ = piIter x.exponent (piIter z.exponent y.numerator) := piIter_commute _ _ _
    _ = piIter x.exponent (piIter y.exponent z.numerator) := congrArg (piIter x.exponent) hyz
    _ = piIter y.exponent (piIter x.exponent z.numerator) := piIter_commute _ _ _
end SameValue
end GaussianParity
