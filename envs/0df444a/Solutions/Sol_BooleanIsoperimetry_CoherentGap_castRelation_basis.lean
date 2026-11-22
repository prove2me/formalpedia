-- Prove2me | solution 1 for BooleanIsoperimetry.CoherentGap.castRelation_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:27:20.347203+00:00
-- url     : https://prove2.me/submissions/8b45273e-ab0b-40cb-939e-f1acdd8ad4cd

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_CoherentGap
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_ConwayGuyCoherentGap

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry BooleanIsoperimetry.CoherentGap
namespace BooleanIsoperimetry.CoherentGap
theorem _root_.solution {firstDimension secondDimension : ℕ}
    (hdimension : firstDimension = secondDimension)
    (coordinate : Fin firstDimension) :
    castRelation hdimension (basis coordinate) =
      basis (Fin.cast hdimension coordinate) := by
  subst secondDimension
  rfl
end BooleanIsoperimetry.CoherentGap
