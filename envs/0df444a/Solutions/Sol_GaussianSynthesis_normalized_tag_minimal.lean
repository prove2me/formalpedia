-- Prove2me | solution 1 for GaussianSynthesis.normalized_tag_minimal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.667798+00:00
-- url     : https://prove2.me/submissions/f3e32504-86b6-4167-a1b7-a32ec9bddecc

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Theorems.Thm_GaussianSynthesis_normalize_sound
import Theorems.Thm_GaussianSynthesis_normalize_canonical
import Theorems.Thm_GaussianSynthesis_canonical_tag_minimal
import Theorems.Thm_GaussianParity_SameValue_trans


set_option autoImplicit true
open GaussianSynthesis
open GaussianParity
namespace GaussianSynthesis
theorem _root_.solution {x y : Fraction} (hxy : SameValue x y) :
    (normalize x).exponent ≤ y.exponent := by
  exact canonical_tag_minimal (normalize_canonical x)
    (SameValue.trans (normalize_sound x) hxy)
end GaussianSynthesis
