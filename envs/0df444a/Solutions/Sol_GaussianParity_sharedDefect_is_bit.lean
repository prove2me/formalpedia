-- Prove2me | solution 1 for GaussianParity.sharedDefect_is_bit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.342874+00:00
-- url     : https://prove2.me/submissions/3935d4f0-9b4e-4fbb-a60f-db1a34964ed8

import Std
import Definitions.Def_DyadicCertificates

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (u v : GInt) :
    sharedDefect u v = 0 ∨ sharedDefect u v = 1 := by
  simp only [sharedDefect]
  omega
end GaussianParity
