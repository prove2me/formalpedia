-- Prove2me | solution 1 for GaussianParity.doubleButterfly_joint_parity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.342874+00:00
-- url     : https://prove2.me/submissions/06617406-d94a-4ebf-94bd-ab1739621500

import Std
import Definitions.Def_DyadicCertificates

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (u v : GInt) :
    (doubleButterfly u v).1.re % 2 = (u.re + u.im + v.re + v.im) % 2 ∧
    (doubleButterfly u v).1.im % 2 = (u.re + u.im + v.re + v.im) % 2 ∧
    (doubleButterfly u v).2.re % 2 = (u.re + u.im + v.re + v.im) % 2 ∧
    (doubleButterfly u v).2.im % 2 = (u.re + u.im + v.re + v.im) % 2 := by
  simp only [doubleButterfly]
  omega
end GaussianParity
