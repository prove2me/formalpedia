-- Prove2me | solution 1 for GaussianSynthesis.normalizeCore_exponent_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.497676+00:00
-- url     : https://prove2.me/submissions/3dbc709f-379d-4e4c-b32d-3ffe3247a05e

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits

set_option autoImplicit true
open GaussianSynthesis
open GaussianParity
namespace GaussianSynthesis
theorem _root_.solution (e : Nat) (z : GInt) :
    (normalizeCore e z).exponent ≤ e := by
  induction e generalizing z with
  | zero => simp [normalizeCore]
  | succ e ih =>
    by_cases h : residue z = 0
    · simp only [normalizeCore, h, ↓reduceIte]
      exact Nat.le_trans (ih _) (Nat.le_succ _)
    · simp [normalizeCore, h]
end GaussianSynthesis
