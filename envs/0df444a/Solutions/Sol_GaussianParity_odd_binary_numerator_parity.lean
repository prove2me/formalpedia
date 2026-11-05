-- Prove2me | solution 1 for GaussianParity.odd_binary_numerator_parity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.497676+00:00
-- url     : https://prove2.me/submissions/eac6e535-961a-4918-a816-9dbb018bb317

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Theorems.Thm_GaussianParity_repeatNegI_residue
import Theorems.Thm_GaussianParity_residue_mulPi
import Theorems.Thm_GaussianParity_residue_zero_iff


set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (q : Nat) (z : GInt) :
    PiDvd (repeatNegI (q+1) (mulPi z)) := by
  apply (residue_zero_iff _).mp
  rw [repeatNegI_residue, residue_mulPi]
end GaussianParity
