-- Prove2me | solution 1 for BooleanIsoperimetry.paperResidualSequence_isResidualShift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:43:52.30666+00:00
-- url     : https://prove2.me/submissions/6e3d5cd0-5e68-4e0c-a684-2d815f139902

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Definitions.Def_LeanPool_BooleanIsoperimetry_LayerWindows
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Combinatorics.SetFamily.Compression.UV
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Compression
public import Theorems.Thm_BooleanIsoperimetry_paperResidualStep_isResidualShift

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} {A A' : Finset (Cube N)}
    (h : IsPaperResidualSequence A A') : IsDownFixedResidualShift A A' := by
  induction h with
  | single hstep => exact paperResidualStep_isResidualShift hstep
  | tail _ hstep ih =>
      have h2 := paperResidualStep_isResidualShift hstep
      exact ⟨by rw [h2.1, ih.1],
             le_trans h2.2.1 ih.2.1,
             lt_trans h2.2.2 ih.2.2⟩
end BooleanIsoperimetry
