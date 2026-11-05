-- Prove2me | solution 1 for GaussianParity.certifiedButterfly_refines
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.342874+00:00
-- url     : https://prove2.me/submissions/c9167fd5-3fbd-441f-aeb5-937f171125ea

import Std
import Definitions.Def_DyadicCertificates
import Theorems.Thm_GaussianParity_butterfly_exact
import Theorems.Thm_GaussianParity_piIter_mulPi

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (u v : GInt) (e : Nat) :
    let p := certifiedButterfly u v e
    SameValue ⟨p.left, p.exponent⟩ ⟨numeratorLeft u v, e + 1⟩ ∧
    SameValue ⟨p.right, p.exponent⟩ ⟨numeratorRight u v, e + 1⟩ := by
  by_cases h : residue u = residue v
  · have hc := butterfly_exact u v h
    simp only [certifiedButterfly, h, ↓reduceIte, SameValue, piIter]
    constructor
    · rw [← piIter_mulPi, hc.1]
    · rw [← piIter_mulPi, hc.2]
  · simp [certifiedButterfly, h, SameValue]
end GaussianParity
