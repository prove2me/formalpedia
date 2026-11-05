-- Prove2me | solution 1 for GaussianSynthesis.normalize_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.497676+00:00
-- url     : https://prove2.me/submissions/abc0c7c5-69d3-4b38-b426-7c072e035e35

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Theorems.Thm_GaussianSynthesis_normalize_sound
import Theorems.Thm_GaussianSynthesis_normalize_canonical
import Theorems.Thm_GaussianSynthesis_canonical_unique
import Theorems.Thm_GaussianParity_SameValue_symm
import Theorems.Thm_GaussianParity_SameValue_trans


set_option autoImplicit true
open GaussianSynthesis
open GaussianParity
namespace GaussianSynthesis
theorem _root_.solution {x y : Fraction} (h : SameValue x y) :
    normalize x = normalize y := by
  apply canonical_unique (normalize_canonical x) (normalize_canonical y)
  exact SameValue.trans (normalize_sound x)
    (SameValue.trans h (SameValue.symm (normalize_sound y)))
end GaussianSynthesis
