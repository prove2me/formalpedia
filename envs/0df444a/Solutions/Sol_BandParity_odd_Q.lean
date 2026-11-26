-- Prove2me | solution 1 for BandParity.odd_Q
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:10:17.494632+00:00
-- url     : https://prove2.me/submissions/e217f5e2-a6a0-4e57-b803-30b5018d6c3f

module
public import Definitions.Def_BandParity_Laws
public import Definitions.Def_BandParity_Main

set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ
omit hp hχ
namespace BandParity
theorem _root_.solution (hp8 : p % 8 = 5) : Odd (Q p) := by
  unfold Q
  rw [Int.odd_coe_nat]
  exact Nat.odd_iff.2 (by omega)
end BandParity
