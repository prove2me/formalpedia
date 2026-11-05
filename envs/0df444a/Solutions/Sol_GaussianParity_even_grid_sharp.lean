-- Prove2me | solution 1 for GaussianParity.even_grid_sharp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.497676+00:00
-- url     : https://prove2.me/submissions/09a2db4b-de8a-45e9-a06e-f492bd2794d8

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Theorems.Thm_GaussianParity_scale_mul
import Theorems.Thm_GaussianParity_repeatPi_even
import Theorems.Thm_GaussianParity_scale_injective

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (q : Nat) :
    ¬ ∃ w : GInt, repeatPi (2*(q+1)) w = scale ((2 : Int)^q) ⟨1,0⟩ := by
  intro ⟨w, hw⟩
  rw [repeatPi_even] at hw
  have hpow : (2 : Int)^(q+1) = (2 : Int)^q * 2 := by simp [Int.pow_succ]
  rw [hpow, ← scale_mul] at hw
  have hcancel := scale_injective ((2 : Int)^q) (Int.pow_ne_zero (by decide)) hw
  have hr := congrArg GInt.re hcancel
  simp only [scale] at hr
  omega
end GaussianParity
