-- Prove2me | solution 1 for BSLambda.ringChar_zmod14011
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T00:52:26.579254+00:00
-- url     : https://prove2.me/submissions/4097bc00-bd3b-4cb0-8a26-9434ede29a03

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


theorem solution : ringChar (ZMod 14011) ≠ 2 := by
  norm_num [ZMod.ringChar_zmod_n]
