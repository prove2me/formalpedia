-- Prove2me | solution 1 for BooleanIsoperimetry.CoherentGap.realDot_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:14:33.58367+00:00
-- url     : https://prove2.me/submissions/32f66419-da32-45fa-a9bb-2a6cf4046d04

module
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Definitions.Def_LeanPool_BooleanIsoperimetry_CoherentGap

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry BooleanIsoperimetry.CoherentGap
namespace BooleanIsoperimetry.CoherentGap
theorem _root_.solution {n : ℕ} (coordinate : Fin n) (candidate : Fin n → ℝ) :
    realDot (basis coordinate) candidate = candidate coordinate := by
  classical
  simp [realDot, basis]
end BooleanIsoperimetry.CoherentGap
