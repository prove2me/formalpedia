-- Prove2me | solution 1 for GaussianSynthesis.per_role_phase_image_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.667798+00:00
-- url     : https://prove2.me/submissions/91413b67-3ec0-4750-975c-6d88f83c26da

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Theorems.Thm_GaussianParity_GInt_ext


set_option autoImplicit true
open GaussianSynthesis
open GaussianParity
namespace GaussianSynthesis
theorem _root_.solution :
    add ⟨-32,0⟩ (gaussianDifference ⟨0,2⟩ ⟨2,0⟩) = ⟨-34,2⟩ ∧
    ¬ ∃ t : GInt, add ⟨-32,0⟩ (gaussianDifference ⟨0,2⟩ ⟨2,0⟩)
      = scale (-32) t := by
  constructor
  · apply GInt.ext <;> simp [add,gaussianDifference,neg]
  · intro ⟨t,ht⟩
    have hr := congrArg GInt.re ht
    simp only [add,gaussianDifference,neg,scale] at hr
    omega
end GaussianSynthesis
