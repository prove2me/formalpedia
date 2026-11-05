-- Prove2me | solution 1 for GaussianSynthesis.canonical_tags_equal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.497676+00:00
-- url     : https://prove2.me/submissions/93111a3f-2f4e-4fcb-a9f2-6d2e7070b2f2

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Theorems.Thm_GaussianSynthesis_positive_piIter_residue
import Theorems.Thm_GaussianParity_SameValue_symm
import Theorems.Thm_GaussianParity_piIter_add
import Theorems.Thm_GaussianParity_piIter_injective


set_option autoImplicit true
open GaussianSynthesis
open GaussianParity
namespace GaussianSynthesis
theorem _root_.solution {x y : Fraction}
    (hx : Canonical x) (hy : Canonical y) (h : SameValue x y) :
    x.exponent = y.exponent := by
  have no_less : ∀ a b : Fraction, Canonical b → SameValue a b →
      ¬ a.exponent < b.exponent := by
    intro a b hb hab hlt
    have hdiff : a.exponent + (b.exponent-a.exponent) = b.exponent := by omega
    have hp : 0 < b.exponent-a.exponent := by omega
    have heq : piIter (b.exponent-a.exponent) a.numerator = b.numerator := by
      apply piIter_injective a.exponent
      rw [← piIter_add, hdiff]
      exact hab
    have hz := positive_piIter_residue (b.exponent-a.exponent) a.numerator hp
    rw [heq] at hz
    simp only [Canonical] at hb
    omega
  have hxy := no_less x y hy h
  have hyx := no_less y x hx (SameValue.symm h)
  omega
end GaussianSynthesis
