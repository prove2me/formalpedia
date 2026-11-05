-- Prove2me | solution 1 for GaussianSynthesis.normalize_idempotent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.497676+00:00
-- url     : https://prove2.me/submissions/edb41fb6-6fef-40b3-a19f-440454e8fca0

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Theorems.Thm_GaussianSynthesis_normalize_canonical
import Theorems.Thm_GaussianSynthesis_normalize_fixed

set_option autoImplicit true
open GaussianSynthesis
open GaussianParity
namespace GaussianSynthesis
theorem _root_.solution (x : Fraction) : normalize (normalize x) = normalize x :=
  normalize_fixed _ (normalize_canonical x)
end GaussianSynthesis
