-- Prove2me | solution 1 for GaussianParity.GInt.ext
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.342874+00:00
-- url     : https://prove2.me/submissions/f7fa4005-c335-4b98-bf7d-707c3fd57924

import Std
import Definitions.Def_DyadicCertificates

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
namespace GInt
theorem _root_.solution {u v : GInt} (hre : u.re = v.re) (him : u.im = v.im) : u = v := by
  cases u; cases v; simp_all
end GInt
end GaussianParity
