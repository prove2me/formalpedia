-- Prove2me | solution 1 for BooleanIsoperimetry.CoherentGap.conwayGuyCertificate_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:41:15.356259+00:00
-- url     : https://prove2.me/submissions/b6f92be1-8cb9-4e08-8f0b-cd578f8a7f23

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_ConwayGuyCoherentGap
public import Definitions.Def_LeanPool_BooleanIsoperimetry_ConwayGuyHeight
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_ConwayGuyRigidity

set_option autoImplicit true
@[expose] public section
public section
open BooleanIsoperimetry BooleanIsoperimetry.CoherentGap
namespace BooleanIsoperimetry.CoherentGap
theorem _root_.solution (dimension : ℕ)
    (coordinate : Fin dimension) :
    Nonempty
      (Certificate (conwayGuyArithmetic.tower.weights dimension)
        (basis coordinate)) :=
  recurrenceCertificate_exists conwayGuyArithmetic.tower
    conwayGuyRecurrence dimension coordinate
end BooleanIsoperimetry.CoherentGap
