-- Prove2me | solution 1 for BSLambda.quadraticChar_neg_one_zmod14011
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:56:24.256797+00:00
-- url     : https://prove2.me/submissions/554c6dbc-30be-4334-adea-5e89a9a9881d

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.Tactic.NormNum.Prime
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Paley_Tournament
public import Theorems.Thm_BSLambda_ringChar_zmod14011

set_option autoImplicit true
@[expose] public section
public section
open Finset
open BSLambda
namespace BSLambda
theorem _root_.solution : quadraticChar (ZMod 14011) (-1) = -1 := by
  rw [quadraticChar_neg_one ringChar_zmod14011, ZMod.card, ZMod.χ₄_nat_eq_if_mod_four]
  norm_num
end BSLambda
