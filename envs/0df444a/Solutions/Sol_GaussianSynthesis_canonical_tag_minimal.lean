-- Prove2me | solution 1 for GaussianSynthesis.canonical_tag_minimal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.667798+00:00
-- url     : https://prove2.me/submissions/e2db855f-b5cc-4304-83d7-b9df1a106f1f

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Theorems.Thm_GaussianSynthesis_normalize_sound
import Theorems.Thm_GaussianSynthesis_normalize_canonical
import Theorems.Thm_GaussianSynthesis_normalizeCore_exponent_bound
import Theorems.Thm_GaussianSynthesis_canonical_tags_equal
import Theorems.Thm_GaussianParity_SameValue_symm
import Theorems.Thm_GaussianParity_SameValue_trans


set_option autoImplicit true
open GaussianSynthesis
open GaussianParity
namespace GaussianSynthesis
theorem _root_.solution {x y : Fraction}
    (hx : Canonical x) (hxy : SameValue x y) : x.exponent ≤ y.exponent := by
  have he : x.exponent = (normalize y).exponent :=
    canonical_tags_equal hx (normalize_canonical y)
      (SameValue.trans hxy (SameValue.symm (normalize_sound y)))
  rw [he]
  exact normalizeCore_exponent_bound y.exponent y.numerator
end GaussianSynthesis
