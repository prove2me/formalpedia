-- Prove2me | solution 1 for ConjCoord.reps_congruence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:02:12.555514+00:00
-- url     : https://prove2.me/submissions/a70cb3af-9edb-4c69-b7e2-86f06c97a8e8

module
public import Definitions.Def_ConjCoord
public import Definitions.Def_ConjCoord_Solution
public import Theorems.Thm_ConjCoord_Proof_reps_congruence


set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord
namespace ConjCoord
theorem _root_.solution (S : SturmInput phi 512) {p : ℕ} (hp : p.Prime) (h5 : p % 16 = 5)
    {a b : ℤ} (hab : a ^ 2 + b ^ 2 = p) (hb : Even b) :
    2 * (reps 1 2 4 p : ℤ) - reps 1 2 2 p ≡ 32 * octA b [ZMOD 64] :=
  Proof.reps_congruence S hp h5 hab hb
end ConjCoord
