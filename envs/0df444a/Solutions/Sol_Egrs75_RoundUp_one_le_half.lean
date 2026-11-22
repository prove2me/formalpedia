-- Prove2me | solution 1 for Egrs75.RoundUp.one_le_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:29:53.433748+00:00
-- url     : https://prove2.me/submissions/f48df084-8624-4fa1-90e5-06f39a12097c

module
public import Definitions.Def_LeanPool_Egrs75_Defs
public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.Data.Finset.Attr
public import Definitions.Def_LeanPool_Egrs75_RoundUp

set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.RoundUp
open Nat
open Egrs75
variable (p : ℕ)
namespace Egrs75.RoundUp
theorem _root_.solution {p : ℕ} (hp : 3 ≤ p) : (1 : ℕ) ≤ (p - 1) / 2 := by
  have : 2 ≤ p - 1 := by omega
  calc (1 : ℕ) = 2 / 2 := by norm_num
    _ ≤ (p - 1) / 2 := Nat.div_le_div_right this
end Egrs75.RoundUp
