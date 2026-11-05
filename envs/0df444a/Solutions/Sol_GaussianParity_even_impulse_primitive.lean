-- Prove2me | solution 1 for GaussianParity.even_impulse_primitive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.497676+00:00
-- url     : https://prove2.me/submissions/1086a428-ba6c-4da4-aadc-6ad185fc2b57

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Theorems.Thm_GaussianParity_repeatNegI_residue
import Theorems.Thm_GaussianParity_binary_one_residue_zero

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (q : Nat) :
    ¬ BinaryDivisible 1 (repeatNegI q ⟨1,0⟩) := by
  intro h
  have hz := binary_one_residue_zero _ h
  rw [repeatNegI_residue] at hz
  simp [residue] at hz
end GaussianParity
