-- Prove2me | solution 1 for BooleanIsoperimetry.CoherentGap.recurrenceCertificate_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:40:18.663084+00:00
-- url     : https://prove2.me/submissions/797de537-2d13-42f2-98e1-22e5d58768cd

module
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Definitions.Def_LeanPool_BooleanIsoperimetry_CoherentGap
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_Certificate_length_eq_dot_target

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry BooleanIsoperimetry.CoherentGap
namespace BooleanIsoperimetry.CoherentGap
theorem _root_.solution (tower : WeightTower)
    (recurrence : FirstCoordinateRecurrence tower) {n : ℕ}
    (coordinate : Fin n) :
    ((recurrenceCertificates tower recurrence n coordinate).relations.length : ℤ) =
      tower.weights n coordinate := by
  exact (recurrenceCertificates tower recurrence n coordinate).length_eq_dot_target.trans
    (dot_basis coordinate (tower.weights n))
end BooleanIsoperimetry.CoherentGap
