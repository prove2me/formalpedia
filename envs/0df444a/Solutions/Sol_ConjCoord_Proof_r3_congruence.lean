-- Prove2me | solution 1 for ConjCoord.Proof.r3_congruence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:01:34.842993+00:00
-- url     : https://prove2.me/submissions/5ae603bb-25d3-461c-a735-14bacfa03705

module
public import Definitions.Def_ConjCoord_Compute
public import Definitions.Def_ConjCoord_TwoSquares
public import Definitions.Def_ConjCoord_Main
public import Theorems.Thm_ConjCoord_Proof_reps_congruence
public import Theorems.Thm_ConjCoord_Proof_lemma3


set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof
namespace ConjCoord.Proof
theorem _root_.solution (S : SturmInput phi 512) {p : ℕ} (hp : p.Prime) (h5 : p % 16 = 5)
    {a b : ℤ} (hab : a ^ 2 + b ^ 2 = p) (hb : Even b) :
    (r3 (2 * p) : ℤ) - r3 p ≡ 96 * octA b [ZMOD 192] := by
  have h := reps_congruence S hp h5 hab hb
  obtain ⟨h1, h2⟩ := lemma3 h5
  have e1 : (r3 p : ℤ) = 3 * reps 1 2 2 p := by exact_mod_cast h1
  have e2 : (r3 (2 * p) : ℤ) = 6 * reps 1 2 4 p := by exact_mod_cast h2
  rw [e1, e2]
  unfold Int.ModEq at *
  omega
end ConjCoord.Proof
