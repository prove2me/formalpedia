-- Prove2me | solution 1 for BooleanIsoperimetry.CoherentGap.castRelation_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:27:19.716693+00:00
-- url     : https://prove2.me/submissions/d5f3c6b8-2951-4bb7-ab40-f40746ff4466

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
    (first second : Relation firstDimension) :
    castRelation hdimension (first - second) =
      castRelation hdimension first - castRelation hdimension second := by
  subst secondDimension
  rfl
end BooleanIsoperimetry.CoherentGap
