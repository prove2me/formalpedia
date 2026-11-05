-- Prove2me | solution 1 for GaussianParity.SameValue.symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.342874+00:00
-- url     : https://prove2.me/submissions/a2d4a658-ebb6-4929-a605-c7b51913557a

import Std
import Definitions.Def_DyadicCertificates

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
namespace SameValue
theorem _root_.solution {x y : Fraction} (h : SameValue x y) : SameValue y x := Eq.symm h
end SameValue
end GaussianParity
