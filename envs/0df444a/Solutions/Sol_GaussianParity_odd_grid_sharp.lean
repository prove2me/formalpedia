-- Prove2me | solution 1 for GaussianParity.odd_grid_sharp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.497676+00:00
-- url     : https://prove2.me/submissions/f7dfbf37-695f-432d-adf6-7b567b42f665

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Theorems.Thm_GaussianParity_repeatPi_odd
import Theorems.Thm_GaussianParity_scale_injective
import Theorems.Thm_GaussianParity_residue_mulPi


set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (q : Nat) :
    ¬ ∃ w : GInt, repeatPi (2*q+1) w = scale ((2 : Int)^q) ⟨1,0⟩ := by
  intro ⟨w, hw⟩
  rw [repeatPi_odd] at hw
  have hcancel := scale_injective ((2 : Int)^q) (Int.pow_ne_zero (by decide)) hw
  have hzero := residue_mulPi (repeatI q w)
  rw [hcancel] at hzero
  simp [residue] at hzero
end GaussianParity
