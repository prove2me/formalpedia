-- Prove2me | solution 1 for GaussianParity.pi_odd_ideal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.497676+00:00
-- url     : https://prove2.me/submissions/d1ac6d5f-fa5b-4caa-a756-f08f8bb433d1

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Theorems.Thm_GaussianParity_repeatI_cancel
import Theorems.Thm_GaussianParity_repeatPi_odd
import Theorems.Thm_GaussianParity_SameValue_symm
import Theorems.Thm_GaussianParity_SameValue_trans
import Theorems.Thm_GaussianParity_dividePi_exact_iff
import Theorems.Thm_GaussianParity_residue_mulPi
import Theorems.Thm_GaussianParity_residue_zero_iff


set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (q : Nat) (z : GInt) :
    PiPowerDivisible (2*q+1) z ↔
      ∃ w : GInt, scale ((2 : Int)^q) w = z ∧ PiDvd w := by
  constructor
  · intro ⟨v, hv⟩
    refine ⟨mulPi (repeatI q v), ?_, ?_⟩
    · exact (repeatPi_odd q v).symm.trans hv
    · exact (residue_zero_iff _).mp (residue_mulPi _)
  · intro ⟨w, hw, hp⟩
    refine ⟨repeatNegI q (dividePi w), ?_⟩
    rw [repeatPi_odd, repeatI_cancel, (dividePi_exact_iff w).mpr hp]
    exact hw
end GaussianParity
