-- Prove2me | solution 1 for GaussianParity.SameValue.refl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.342874+00:00
-- url     : https://prove2.me/submissions/5ce7236f-d85f-438f-b354-bb1cf131c2ab

import Std
import Definitions.Def_DyadicCertificates

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
namespace SameValue
theorem _root_.solution (x : Fraction) : SameValue x x := rfl
end SameValue
end GaussianParity
