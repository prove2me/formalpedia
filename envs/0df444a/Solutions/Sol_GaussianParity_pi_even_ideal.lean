-- Prove2me | solution 1 for GaussianParity.pi_even_ideal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.497676+00:00
-- url     : https://prove2.me/submissions/32778b66-105f-41c4-9f9b-dfd7377a8af1

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Theorems.Thm_GaussianParity_repeatPi_even
import Theorems.Thm_GaussianParity_repeatI_cancel
import Theorems.Thm_GaussianParity_SameValue_symm
import Theorems.Thm_GaussianParity_SameValue_trans


set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (q : Nat) (z : GInt) :
    PiPowerDivisible (2*q) z ↔ BinaryDivisible q z := by
  constructor
  · intro ⟨w, hw⟩
    exact ⟨repeatI q w, (repeatPi_even q w).symm.trans hw⟩
  · intro ⟨w, hw⟩
    refine ⟨repeatNegI q w, ?_⟩
    rw [repeatPi_even, repeatI_cancel]
    exact hw
end GaussianParity
