-- Prove2me | solution 1 for GaussianSynthesis.canonical_inverse_restores
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.667798+00:00
-- url     : https://prove2.me/submissions/509a5040-6df2-4548-a0d7-85c84e057116

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Theorems.Thm_GaussianSynthesis_normalize_congr
import Theorems.Thm_GaussianSynthesis_heterogeneous_inverse_restores

set_option autoImplicit true
open GaussianSynthesis
open GaussianParity
namespace GaussianSynthesis
theorem _root_.solution (x y : Fraction) :
    normalize (packedLeft (rawCInverse (rawAlignedC x y))) = normalize x ∧
    normalize (packedRight (rawCInverse (rawAlignedC x y))) = normalize y := by
  have h := heterogeneous_inverse_restores x y
  exact ⟨normalize_congr h.1,normalize_congr h.2⟩
end GaussianSynthesis
