-- Prove2me | solution 1 for GaussianParity.changed_pairing_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.342874+00:00
-- url     : https://prove2.me/submissions/ef67a7d3-c9e3-46e0-8de4-2798dc6ee143

import Std
import Definitions.Def_DyadicCertificates

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution :
    SameResidue ⟨1, 0⟩ ⟨1, 0⟩ ∧ SameResidue ⟨1, 0⟩ ⟨0, 1⟩ ∧
    ¬ SameResidue (butterfly ⟨1, 0⟩ ⟨1, 0⟩).1
       (butterfly ⟨1, 0⟩ ⟨0, 1⟩).1 := by
  simp [SameResidue, residue, butterfly, dividePi, numeratorLeft, numeratorRight, add, mulI]
end GaussianParity
