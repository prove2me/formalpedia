-- Prove2me | solution 1 for ConjCoord.conjecture_coord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:06:26.222114+00:00
-- url     : https://prove2.me/submissions/50d2c3d5-0f5a-4b6e-be23-86db1e23be02

module
public import Definitions.Def_ConjCoord
public import Definitions.Def_ConjCoord_Solution
public import Theorems.Thm_ConjCoord_Proof_conjecture_coord


set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord
namespace ConjCoord
theorem _root_.solution (S : SturmInput phi 512) {p : ℕ} (hp : p.Prime) (h5 : p % 16 = 5)
    {a b : ℤ} (hab : a ^ 2 + b ^ 2 = p) (hb : Even b) {h h' : ℕ}
    (hG : r3 p = 12 * h) (hG' : r3 (2 * p) = 12 * h') (V : Prop)
    (hV : V ↔ (h' : ℤ) - h ≡ 8 * (if p % 32 = 5 then 1 else 0) [ZMOD 16]) :
    V ↔ ((b % 16 = 6 ∨ b % 16 = 10) ↔ ¬ p % 32 = 21) :=
  Proof.conjecture_coord S hp h5 hab hb hG hG' V hV
end ConjCoord
