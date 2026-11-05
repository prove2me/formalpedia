-- Prove2me | solution 1 for GaussianSynthesis.two_pi_numerator_sameValue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.667798+00:00
-- url     : https://prove2.me/submissions/4e2c4399-3054-4171-81d9-125262ffaf3f

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Theorems.Thm_GaussianParity_piIter_mulPi


set_option autoImplicit true
open GaussianSynthesis
open GaussianParity
namespace GaussianSynthesis
theorem _root_.solution (z : GInt) (e : Nat) :
    SameValue ⟨mulPi (mulPi z),e+2⟩ ⟨z,e⟩ := by
  simp only [SameValue]
  rw [piIter_mulPi, piIter_mulPi]
  rfl
end GaussianSynthesis
