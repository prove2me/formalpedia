-- Prove2me | solution 1 for GaussianSynthesis.normalizeCore_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.497676+00:00
-- url     : https://prove2.me/submissions/774ef1f0-7194-4983-909a-624c6ef5b7b3

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Theorems.Thm_GaussianSynthesis_cancelPi_sameValue
import Theorems.Thm_GaussianParity_SameValue_refl
import Theorems.Thm_GaussianParity_SameValue_trans


set_option autoImplicit true
open GaussianSynthesis
open GaussianParity
namespace GaussianSynthesis
theorem _root_.solution (e : Nat) (z : GInt) :
    SameValue (normalizeCore e z) ⟨z, e⟩ := by
  induction e generalizing z with
  | zero => exact SameValue.refl _
  | succ e ih =>
    by_cases h : residue z = 0
    · simp only [normalizeCore, h, ↓reduceIte]
      exact SameValue.trans (ih _) (cancelPi_sameValue z e h)
    · simp only [normalizeCore, h, ↓reduceIte]
      exact SameValue.refl _
end GaussianSynthesis
