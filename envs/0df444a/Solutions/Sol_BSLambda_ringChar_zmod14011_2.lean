-- Prove2me | solution 2 for BSLambda.ringChar_zmod14011
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:52:34.20021+00:00
-- url     : https://prove2.me/submissions/fe93760f-b837-4166-b338-8114f633300c

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.Tactic.NormNum.Prime
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Paley_Tournament

set_option autoImplicit true
@[expose] public section
public section
open Finset
open BSLambda
namespace BSLambda
theorem _root_.solution : ringChar (ZMod 14011) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]
  norm_num only
end BSLambda
