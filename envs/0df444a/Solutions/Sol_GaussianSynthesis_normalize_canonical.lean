-- Prove2me | solution 1 for GaussianSynthesis.normalize_canonical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.497676+00:00
-- url     : https://prove2.me/submissions/c2a6c8b1-c36b-40d5-b13c-0a1d9d6492d0

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Theorems.Thm_GaussianSynthesis_normalizeCore_canonical

set_option autoImplicit true
open GaussianSynthesis
open GaussianParity
namespace GaussianSynthesis
theorem _root_.solution (x : Fraction) : Canonical (normalize x) :=
  normalizeCore_canonical _ _
end GaussianSynthesis
