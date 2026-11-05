-- Prove2me | solution 1 for GaussianParity.piIter_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.342874+00:00
-- url     : https://prove2.me/submissions/2167ce21-4226-4127-aa11-e3946e53bf36

import Std
import Definitions.Def_DyadicCertificates
import Theorems.Thm_GaussianParity_mulPi_injective

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (n : Nat) {u v : GInt} (h : piIter n u = piIter n v) : u = v := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih (mulPi_injective h)
end GaussianParity
