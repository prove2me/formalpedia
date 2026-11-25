-- Prove2me | solution 1 for ConjCoord.class_number_congruence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:03:37.288086+00:00
-- url     : https://prove2.me/submissions/1d357678-0575-41da-81cc-5f9eea565cc4

module
public import Definitions.Def_ConjCoord
public import Definitions.Def_ConjCoord_Solution
public import Theorems.Thm_ConjCoord_Proof_class_number_congruence


set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord
namespace ConjCoord
theorem _root_.solution (S : SturmInput phi 512) {p : ℕ} (hp : p.Prime)
    (h5 : p % 16 = 5) {a b : ℤ} (hab : a ^ 2 + b ^ 2 = p) (hb : Even b) {h h' : ℕ}
    (hG : r3 p = 12 * h) (hG' : r3 (2 * p) = 12 * h') :
    (h' : ℤ) ≡ h + 8 * octA b [ZMOD 16] :=
  Proof.class_number_congruence S hp h5 hab hb hG hG'
end ConjCoord
