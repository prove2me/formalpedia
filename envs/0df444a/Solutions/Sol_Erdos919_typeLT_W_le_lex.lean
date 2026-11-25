-- Prove2me | solution 1 for Erdos919.typeLT_W_le_lex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:34:44.9192+00:00
-- url     : https://prove2.me/submissions/9c4d9c5c-3ab4-4b5e-8d23-0bc0bb19da30

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919
noncomputable section
namespace Erdos919
theorem _root_.solution : typeLT W.{u} ≤ typeLT (W.{u} ×ₗ W.{u}) :=
  type_le_iff'.2 ⟨(OrderEmbedding.ofStrictMono (fun i : W.{u} => toLex (i, i))
    (fun _ _ h => Prod.Lex.toLex_lt_toLex.2 (Or.inl h))).ltEmbedding⟩
end Erdos919
