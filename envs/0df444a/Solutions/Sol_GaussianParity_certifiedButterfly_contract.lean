-- Prove2me | solution 1 for GaussianParity.certifiedButterfly_contract
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.342874+00:00
-- url     : https://prove2.me/submissions/46611631-008e-41ba-922d-178418d5551d

import Std
import Definitions.Def_DyadicCertificates
import Theorems.Thm_GaussianParity_butterfly_exact

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (u v : GInt) (e : Nat) :
    let p := certifiedButterfly u v e
    (p.exponent = e ∧ mulPi p.left = numeratorLeft u v ∧
      mulPi p.right = numeratorRight u v) ∨
    (p.exponent = e + 1 ∧ p.left = numeratorLeft u v ∧ p.right = numeratorRight u v) := by
  by_cases h : residue u = residue v
  · left
    have hc := butterfly_exact u v h
    simp [certifiedButterfly, h, hc.1, hc.2]
  · right
    simp [certifiedButterfly, h]
end GaussianParity
