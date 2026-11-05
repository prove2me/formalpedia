-- Prove2me | solution 1 for GaussianParity.butterfly_square
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.342874+00:00
-- url     : https://prove2.me/submissions/94f451d9-d0a9-4a3c-876d-fbd92bf15a39

import Std
import Definitions.Def_DyadicCertificates
import Theorems.Thm_GaussianParity_GInt_ext

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (u v : GInt) (h : SameResidue u v) :
    butterfly (butterfly u v).1 (butterfly u v).2 = (v, u) := by
  apply Prod.ext
  · apply GInt.ext
    · simp only [butterfly, dividePi, numeratorLeft, numeratorRight, add, mulI,
        SameResidue, residue] at *
      omega
    · simp only [butterfly, dividePi, numeratorLeft, numeratorRight, add, mulI,
        SameResidue, residue] at *
      omega
  · apply GInt.ext
    · simp only [butterfly, dividePi, numeratorLeft, numeratorRight, add, mulI,
        SameResidue, residue] at *
      omega
    · simp only [butterfly, dividePi, numeratorLeft, numeratorRight, add, mulI,
        SameResidue, residue] at *
      omega
end GaussianParity
