-- Prove2me | solution 1 for GaussianSynthesis.normalize_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.497676+00:00
-- url     : https://prove2.me/submissions/86822769-0d22-411a-ba0c-c9f0168227de

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits

set_option autoImplicit true
open GaussianSynthesis
open GaussianParity
namespace GaussianSynthesis
theorem _root_.solution (e : Nat) : normalize ⟨⟨0,0⟩,e⟩ = ⟨⟨0,0⟩,0⟩ := by
  unfold normalize
  induction e with
  | zero => rfl
  | succ e ih => simpa [normalizeCore, residue, dividePi] using ih
end GaussianSynthesis
