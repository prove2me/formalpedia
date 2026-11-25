-- Prove2me | solution 1 for Erdos919.mk_lex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:34:50.462439+00:00
-- url     : https://prove2.me/submissions/b0eaa43e-6b68-442a-877d-cc2505bc5c0d

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution
public import Theorems.Thm_Erdos919_mk_W
public import Theorems.Thm_Erdos919_equiv_lex

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919
noncomputable section
namespace Erdos919
theorem _root_.solution : #(W.{u} ×ₗ W.{u}) = ℵ_ 2 := by
  obtain ⟨e⟩ := equiv_lex.{u}
  rw [← mk_congr e, mk_W]
end Erdos919
