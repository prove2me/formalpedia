-- Prove2me | solution 1 for BooleanIsoperimetry.CoherentGap.conwayGuyNormalizedChamberRigidity_of_blockIdentity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:41:12.595946+00:00
-- url     : https://prove2.me/submissions/6f6c41f3-4c33-437e-9c81-f7b38c44c4a2

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_ConwayGuyCoherentGap
public import Definitions.Def_LeanPool_BooleanIsoperimetry_ConwayGuyHeight
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_ConwayGuyRigidity
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_normalizedChamberRigidity


set_option autoImplicit true
@[expose] public section
public section
open BooleanIsoperimetry BooleanIsoperimetry.CoherentGap
namespace BooleanIsoperimetry.CoherentGap
theorem _root_.solution
    (hblock : ∀ offset, ConwayGuyBlockIdentity offset) {n : ℕ}
    (candidate : Fin n → ℝ)
    (hgap : ∀ relation,
      IsLiftableUnit (conwayGuyArithmetic.tower.weights n) relation →
        1 ≤ realDot relation candidate) :
    ∀ coordinate,
      (conwayGuyArithmetic.tower.weights n coordinate : ℝ) ≤
        candidate coordinate :=
  normalizedChamberRigidity conwayGuyArithmetic.tower
    (conwayGuyFirstCoordinateRecurrence hblock) candidate hgap
end BooleanIsoperimetry.CoherentGap
