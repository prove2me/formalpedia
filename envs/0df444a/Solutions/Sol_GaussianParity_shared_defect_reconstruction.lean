-- Prove2me | solution 1 for GaussianParity.shared_defect_reconstruction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.342874+00:00
-- url     : https://prove2.me/submissions/9cf36a8d-bc13-4cbf-9de0-da2cc637d26a

import Std
import Definitions.Def_DyadicCertificates

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (u v : GInt) :
    let n := doubleButterfly u v
    let epsilon := sharedDefect u v
    n.1.re = 2 * (n.1.re / 2) + epsilon ∧
    n.1.im = 2 * (n.1.im / 2) + epsilon ∧
    n.2.re = 2 * (n.2.re / 2) + epsilon ∧
    n.2.im = 2 * (n.2.im / 2) + epsilon := by
  simp only [doubleButterfly, sharedDefect]
  omega
end GaussianParity
