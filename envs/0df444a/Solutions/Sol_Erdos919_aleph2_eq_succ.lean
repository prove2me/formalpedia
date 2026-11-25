-- Prove2me | solution 1 for Erdos919.aleph2_eq_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:13:46.315031+00:00
-- url     : https://prove2.me/submissions/a5e5de71-a579-4178-8db3-cc01a6f92329

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
theorem _root_.solution : (ℵ_ 2 : Cardinal.{u}) = Order.succ ℵ₁ := by
  rw [succ_aleph, one_add_one_eq_two]
end Erdos919
