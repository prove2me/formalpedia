-- Prove2me | solution 1 for Erdos919.smallCard_of_smallType
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:36:43.865867+00:00
-- url     : https://prove2.me/submissions/7a75882d-95cc-4f40-bae2-a1cb800ca206

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution
public import Theorems.Thm_Erdos919_aleph1_lt_aleph2
public import Theorems.Thm_Erdos919_typeLT_W_le_lex

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919
noncomputable section
namespace Erdos919
theorem _root_.solution {G : SimpleGraph (W.{u} ×ₗ W.{u})} (hG : SmallTypeCC G) :
    SmallCardCC G := by
  intro X hX
  apply hG X
  rw [← typeLT_lex]
  calc typeLT X < (ℵ_ 2 : Cardinal.{u}).ord :=
        lt_ord.2 (by rw [card_type]; exact lt_of_le_of_lt hX aleph1_lt_aleph2)
    _ = typeLT W.{u} := (type_toType _).symm
    _ ≤ typeLT (W.{u} ×ₗ W.{u}) := typeLT_W_le_lex
end Erdos919
