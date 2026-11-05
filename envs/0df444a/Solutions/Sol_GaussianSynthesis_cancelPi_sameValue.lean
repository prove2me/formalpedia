-- Prove2me | solution 1 for GaussianSynthesis.cancelPi_sameValue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.497676+00:00
-- url     : https://prove2.me/submissions/4f293f36-a6c6-43b2-8006-cdbec6590764

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Theorems.Thm_GaussianParity_dividePi_exact_iff
import Theorems.Thm_GaussianParity_piIter_mulPi
import Theorems.Thm_GaussianParity_residue_zero_iff


set_option autoImplicit true
open GaussianSynthesis
open GaussianParity
namespace GaussianSynthesis
theorem _root_.solution (z : GInt) (e : Nat) (h : residue z = 0) :
    SameValue ⟨dividePi z, e⟩ ⟨z, e+1⟩ := by
  have hx := (dividePi_exact_iff z).mpr ((residue_zero_iff z).mp h)
  simp only [SameValue, piIter]
  rw [← piIter_mulPi, hx]
end GaussianSynthesis
