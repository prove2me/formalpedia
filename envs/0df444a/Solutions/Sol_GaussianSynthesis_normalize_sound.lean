-- Prove2me | solution 1 for GaussianSynthesis.normalize_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.497676+00:00
-- url     : https://prove2.me/submissions/6f98c435-f08f-4116-8ef8-b80f6baef7fe

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Theorems.Thm_GaussianSynthesis_normalizeCore_sound

set_option autoImplicit true
open GaussianSynthesis
open GaussianParity
namespace GaussianSynthesis
theorem _root_.solution (x : Fraction) : SameValue (normalize x) x := by
  exact normalizeCore_sound x.exponent x.numerator
end GaussianSynthesis
