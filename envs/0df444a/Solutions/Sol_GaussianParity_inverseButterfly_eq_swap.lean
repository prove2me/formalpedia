-- Prove2me | solution 1 for GaussianParity.inverseButterfly_eq_swap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.342874+00:00
-- url     : https://prove2.me/submissions/371e177b-6b4f-4b2b-b934-e607c727280e

import Std
import Definitions.Def_DyadicCertificates
import Theorems.Thm_GaussianParity_GInt_ext

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (u v : GInt) (h : SameResidue u v) :
    inverseButterfly u v = ((butterfly u v).2, (butterfly u v).1) := by
  apply Prod.ext <;> apply GInt.ext <;>
    simp only [inverseButterfly, neg, mulNegI, butterfly, dividePi, numeratorLeft,
      numeratorRight, add, mulI, SameResidue, residue] at * <;> omega
end GaussianParity
