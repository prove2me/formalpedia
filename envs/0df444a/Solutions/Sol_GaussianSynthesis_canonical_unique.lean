-- Prove2me | solution 1 for GaussianSynthesis.canonical_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.497676+00:00
-- url     : https://prove2.me/submissions/9db81713-8eaf-45eb-a7e4-e916c90cdc67

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Theorems.Thm_GaussianSynthesis_canonical_tags_equal
import Theorems.Thm_GaussianParity_piIter_injective


set_option autoImplicit true
open GaussianSynthesis
open GaussianParity
namespace GaussianSynthesis
theorem _root_.solution {x y : Fraction}
    (hx : Canonical x) (hy : Canonical y) (h : SameValue x y) : x = y := by
  have he := canonical_tags_equal hx hy h
  have hn : x.numerator = y.numerator := by
    apply piIter_injective x.exponent
    unfold SameValue at h
    rw [← he] at h
    exact h
  cases x; cases y; simp_all
end GaussianSynthesis
