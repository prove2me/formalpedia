-- Prove2me | solution 1 for Erdos266.quad_dom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:43:18.557637+00:00
-- url     : https://prove2.me/submissions/b95200f2-acb5-40d3-ba5e-7b5ee60ef24c

module
public import Definitions.Def_Erdos266_Defs
public import Definitions.Def_Erdos266_Growth

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution (c₀ c₁ : ℕ) : ∀ k, c₀ + c₁ + 2 ≤ k → c₁ * k + c₀ ≤ k * k := by
  intro k hk
  calc c₁ * k + c₀ ≤ c₁ * k + k := by omega
  _ = (c₁ + 1) * k := by ring
  _ ≤ k * k := Nat.mul_le_mul_right k (by omega)
end Erdos266
