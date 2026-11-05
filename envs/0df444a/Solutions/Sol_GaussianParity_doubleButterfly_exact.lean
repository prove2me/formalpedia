-- Prove2me | solution 1 for GaussianParity.doubleButterfly_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.342874+00:00
-- url     : https://prove2.me/submissions/81732ac0-830c-4131-a726-7d648d06e31e

import Std
import Definitions.Def_DyadicCertificates
import Theorems.Thm_GaussianParity_GInt_ext

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (u v : GInt) (h : SameResidue u v) :
    doubleButterfly u v = (scaleTwo (butterfly u v).1, scaleTwo (butterfly u v).2) := by
  apply Prod.ext <;> apply GInt.ext <;>
    simp only [doubleButterfly, scaleTwo, butterfly, dividePi, numeratorLeft,
      numeratorRight, add, mulI, SameResidue, residue] at * <;> omega
end GaussianParity
