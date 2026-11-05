-- Prove2me | solution 1 for GaussianParity.repeatPi_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.497676+00:00
-- url     : https://prove2.me/submissions/d630c595-b387-48c6-8e7b-eb87423c8fdf

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Theorems.Thm_GaussianParity_mulPi_square
import Theorems.Thm_GaussianParity_mulI_scale
import Theorems.Thm_GaussianParity_scale_mul

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (q : Nat) (z : GInt) :
    repeatPi (2*q) z = scale ((2 : Int)^q) (repeatI q z) := by
  induction q with
  | zero => simp [repeatPi, repeatI, scale]
  | succ q ih =>
    have hn : 2*(q+1) = 2*q+1+1 := by omega
    rw [hn]
    simp only [repeatPi]
    rw [mulPi_square, ih, mulI_scale, scale_mul]
    simp [repeatI, Int.pow_succ, Int.mul_comm]
end GaussianParity
