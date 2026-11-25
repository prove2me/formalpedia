-- Prove2me | solution 1 for Erdos919.equiv_lex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:19:27.694025+00:00
-- url     : https://prove2.me/submissions/6c535ac0-1620-4b61-8ac7-9bd72b62c41a

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution
public import Theorems.Thm_Erdos919_mk_W

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919
noncomputable section
namespace Erdos919
theorem _root_.solution : Nonempty (W.{u} ≃ W.{u} ×ₗ W.{u}) := by
  apply Cardinal.eq.1
  rw [← mk_congr (toLex : W.{u} × W.{u} ≃ W.{u} ×ₗ W.{u}), mk_prod, Cardinal.lift_id, mk_W,
    mul_eq_self (aleph0_le_aleph 2)]
end Erdos919
