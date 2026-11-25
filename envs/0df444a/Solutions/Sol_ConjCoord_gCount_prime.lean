-- Prove2me | solution 1 for ConjCoord.gCount_prime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:57:22.670594+00:00
-- url     : https://prove2.me/submissions/38d5a95e-a19a-4f98-a1ef-b3b710cb875e

module
public import Definitions.Def_ConjCoord
public import Definitions.Def_ConjCoord_Solution
public import Theorems.Thm_ConjCoord_Proof_gCount_prime


set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord
namespace ConjCoord
theorem _root_.solution {p : ℕ} (hp : p.Prime) (h5 : p % 16 = 5) {a b : ℤ}
    (hab : a ^ 2 + b ^ 2 = p) (hb : Even b) :
    (gCount p : ℤ) ≡ 4 * octA b [ZMOD 8] :=
  Proof.gCount_prime hp h5 hab hb
end ConjCoord
