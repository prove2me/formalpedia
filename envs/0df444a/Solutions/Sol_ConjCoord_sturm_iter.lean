-- Prove2me | solution 1 for ConjCoord.sturm_iter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:55:58.384617+00:00
-- url     : https://prove2.me/submissions/3bf2ec59-6e16-476b-8c36-55ebc78b4d4a

module
public import Definitions.Def_ConjCoord
public import Definitions.Def_ConjCoord_Solution
public import Theorems.Thm_ConjCoord_Proof_sturm_iter


set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord
namespace ConjCoord
theorem _root_.solution {f : ℕ → ℤ} {B : ℕ} (S : SturmInput f B) (k : ℕ) :
    ∀ g ∈ S.M, (∀ n ≤ B, (2 : ℤ) ^ k ∣ g n) → ∀ n, (2 : ℤ) ^ k ∣ g n :=
  Proof.sturm_iter S k
end ConjCoord
