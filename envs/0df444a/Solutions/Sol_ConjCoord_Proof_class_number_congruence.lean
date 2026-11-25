-- Prove2me | solution 1 for ConjCoord.Proof.class_number_congruence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:01:33.009881+00:00
-- url     : https://prove2.me/submissions/85c508fc-d91b-424b-8697-aeecfed552fb

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
theorem _root_.solution (S : SturmInput phi 512) {p : ℕ} (hp : p.Prime)
    (h5 : p % 16 = 5) {a b : ℤ} (hab : a ^ 2 + b ^ 2 = p) (hb : Even b) {h h' : ℕ}
    (hG : r3 p = 12 * h) (hG' : r3 (2 * p) = 12 * h') :
    (h' : ℤ) ≡ h + 8 * octA b [ZMOD 16] := by
  have hc := reps_congruence S hp h5 hab hb
  obtain ⟨h1, h2⟩ := lemma3 h5
  have e1 : (reps 1 2 2 p : ℤ) = 4 * h := by
    have : reps 1 2 2 p = 4 * h := by omega
    exact_mod_cast this
  have e2 : (reps 1 2 4 p : ℤ) = 2 * h' := by
    have : reps 1 2 4 p = 2 * h' := by omega
    exact_mod_cast this
  rw [e1, e2] at hc
  unfold Int.ModEq at *
  omega
end ConjCoord.Proof
