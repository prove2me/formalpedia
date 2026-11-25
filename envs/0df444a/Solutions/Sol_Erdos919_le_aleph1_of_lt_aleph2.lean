-- Prove2me | solution 1 for Erdos919.le_aleph1_of_lt_aleph2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:30:51.861114+00:00
-- url     : https://prove2.me/submissions/9619a745-611e-4012-86c0-1d8f58824bb8

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
theorem _root_.solution {c : Cardinal.{u}} (h : c < ℵ_ 2) : c ≤ ℵ₁ := by
  rw [aleph2_eq_succ] at h; exact Order.lt_succ_iff.1 h
end Erdos919
