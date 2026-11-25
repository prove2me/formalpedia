-- Prove2me | solution 1 for Erdos919.aleph1_lt_aleph2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:20:31.828492+00:00
-- url     : https://prove2.me/submissions/a814e2fb-5c6b-45c6-a9c0-a073c94b3a53

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution
public import Theorems.Thm_Erdos919_aleph2_eq_succ

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919
noncomputable section
namespace Erdos919
theorem _root_.solution : (ℵ₁ : Cardinal.{u}) < ℵ_ 2 := by
  rw [aleph2_eq_succ]; exact Order.lt_succ _
end Erdos919
