-- Prove2me | solution 1 for ConjCoord.r3_congruence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:03:26.502804+00:00
-- url     : https://prove2.me/submissions/4adeb41f-2a92-46bb-af40-9bab2f2fac95

module
public import Definitions.Def_ConjCoord
public import Definitions.Def_ConjCoord_Solution
public import Theorems.Thm_ConjCoord_Proof_r3_congruence


set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord
namespace ConjCoord
theorem _root_.solution (S : SturmInput phi 512) {p : ℕ} (hp : p.Prime) (h5 : p % 16 = 5)
    {a b : ℤ} (hab : a ^ 2 + b ^ 2 = p) (hb : Even b) :
    (r3 (2 * p) : ℤ) - r3 p ≡ 96 * octA b [ZMOD 192] :=
  Proof.r3_congruence S hp h5 hab hb
end ConjCoord
