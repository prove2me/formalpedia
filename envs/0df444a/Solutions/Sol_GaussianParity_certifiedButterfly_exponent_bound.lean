-- Prove2me | solution 1 for GaussianParity.certifiedButterfly_exponent_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.342874+00:00
-- url     : https://prove2.me/submissions/7a560c97-dbbd-449f-9bba-1eb928e377eb

import Std
import Definitions.Def_DyadicCertificates

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (u v : GInt) (e : Nat) :
    e ≤ (certifiedButterfly u v e).exponent ∧
    (certifiedButterfly u v e).exponent ≤ e + 1 := by
  unfold certifiedButterfly
  split <;> simp <;> omega
end GaussianParity
