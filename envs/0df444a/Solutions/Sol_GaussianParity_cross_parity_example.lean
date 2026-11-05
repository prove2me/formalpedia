-- Prove2me | solution 1 for GaussianParity.cross_parity_example
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.342874+00:00
-- url     : https://prove2.me/submissions/eaa83444-1662-4453-88dc-2939051300a4

import Std
import Definitions.Def_DyadicCertificates

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution :
    SameResidue ⟨1, 0⟩ ⟨0, 1⟩ ∧
    (⟨1, 0⟩ : GInt).re % 2 ≠ (⟨0, 1⟩ : GInt).re % 2 ∧
    butterfly ⟨1, 0⟩ ⟨0, 1⟩ = (⟨1, 1⟩, ⟨0, 0⟩) := by
  simp [SameResidue, residue, butterfly, dividePi, numeratorLeft, numeratorRight, add, mulI]
end GaussianParity
