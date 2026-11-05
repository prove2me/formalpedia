-- Prove2me | solution 1 for GaussianSynthesis.normalizeCore_canonical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.497676+00:00
-- url     : https://prove2.me/submissions/243afd1d-5bbe-4e5b-b9f4-50a55d38f8e1

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits

set_option autoImplicit true
open GaussianSynthesis
open GaussianParity
namespace GaussianSynthesis
theorem _root_.solution (e : Nat) (z : GInt) :
    Canonical (normalizeCore e z) := by
  induction e generalizing z with
  | zero => exact Or.inl rfl
  | succ e ih =>
    by_cases h : residue z = 0
    · simp only [normalizeCore, h, ↓reduceIte]
      exact ih _
    · simp only [normalizeCore, h, ↓reduceIte, Canonical]
      exact Or.inr h
end GaussianSynthesis
