-- Prove2me | solution 1 for GaussianParity.butterfly_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.342874+00:00
-- url     : https://prove2.me/submissions/b4637017-13b2-47cf-93fd-576626fda852

import Std
import Definitions.Def_DyadicCertificates
import Theorems.Thm_GaussianParity_dividePi_exact_iff
import Theorems.Thm_GaussianParity_butterfly_integral_iff

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (u v : GInt) (h : SameResidue u v) :
    mulPi (butterfly u v).1 = numeratorLeft u v ∧
    mulPi (butterfly u v).2 = numeratorRight u v := by
  have hp := (butterfly_integral_iff u v).mpr h
  exact ⟨(dividePi_exact_iff _).mpr hp.1, (dividePi_exact_iff _).mpr hp.2⟩
end GaussianParity
