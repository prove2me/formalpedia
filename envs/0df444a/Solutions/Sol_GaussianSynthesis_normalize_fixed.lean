-- Prove2me | solution 1 for GaussianSynthesis.normalize_fixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.497676+00:00
-- url     : https://prove2.me/submissions/a77433c9-fbe7-4cd4-9400-9239a726e496

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits

set_option autoImplicit true
open GaussianSynthesis
open GaussianParity
namespace GaussianSynthesis
theorem _root_.solution (x : Fraction) (h : Canonical x) : normalize x = x := by
  cases x with
  | mk z e =>
    cases e with
    | zero => rfl
    | succ e =>
      have hz : residue z ≠ 0 := by
        simp only [Canonical] at h
        omega
      simp [normalize, normalizeCore, hz]
end GaussianSynthesis
