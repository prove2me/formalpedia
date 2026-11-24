-- Prove2me | solution 1 for BSLambda.paley_isDR
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:11:36.016896+00:00
-- url     : https://prove2.me/submissions/717751d7-1699-48b3-933b-d9003b6229c7

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.Tactic.NormNum.Prime
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Paley_Tournament
public import Theorems.Thm_BSLambda_ringChar_zmod14011
public import Theorems.Thm_BSLambda_quadraticChar_neg_one_zmod14011
public import Theorems.Thm_BSLambda_paleyArc_isDRTournamentWith

set_option autoImplicit true
@[expose] public section
public section
open Finset
open BSLambda
namespace BSLambda
theorem _root_.solution : IsDRTournamentWith (paleyArc 14011) 7005 3502 :=
  paleyArc_isDRTournamentWith ringChar_zmod14011 quadraticChar_neg_one_zmod14011 rfl rfl
end BSLambda
