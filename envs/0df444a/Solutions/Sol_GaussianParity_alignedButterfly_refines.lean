-- Prove2me | solution 1 for GaussianParity.alignedButterfly_refines
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.497676+00:00
-- url     : https://prove2.me/submissions/08efe1ba-e96e-4d3e-afe0-e8ef5ce20305

import Std
import Definitions.Def_DyadicCertificates
import Theorems.Thm_GaussianParity_certifiedButterfly_refines

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (x y : Fraction) :
    let e := commonExponent x y
    let u := (raiseTo x e).numerator
    let v := (raiseTo y e).numerator
    let p := alignedButterfly x y
    SameValue ⟨p.left, p.exponent⟩ ⟨numeratorLeft u v, e + 1⟩ ∧
    SameValue ⟨p.right, p.exponent⟩ ⟨numeratorRight u v, e + 1⟩ := by
  exact certifiedButterfly_refines _ _ _
end GaussianParity
