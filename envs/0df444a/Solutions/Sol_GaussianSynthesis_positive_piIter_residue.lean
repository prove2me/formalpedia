-- Prove2me | solution 1 for GaussianSynthesis.positive_piIter_residue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.497676+00:00
-- url     : https://prove2.me/submissions/adeb9fbd-bdc8-421e-a42d-b8acff7cd54c

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Theorems.Thm_GaussianParity_residue_mulPi


set_option autoImplicit true
open GaussianSynthesis
open GaussianParity
namespace GaussianSynthesis
theorem _root_.solution (e : Nat) (z : GInt) (h : 0 < e) :
    residue (piIter e z) = 0 := by
  cases e with
  | zero => omega
  | succ e => exact residue_mulPi _
end GaussianSynthesis
