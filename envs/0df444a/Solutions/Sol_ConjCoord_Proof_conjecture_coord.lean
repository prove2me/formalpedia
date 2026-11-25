-- Prove2me | solution 1 for ConjCoord.Proof.conjecture_coord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:02:48.143885+00:00
-- url     : https://prove2.me/submissions/c13aeaaf-210a-4d96-9a71-efaf142dfd30

module
public import Definitions.Def_ConjCoord_Compute
public import Definitions.Def_ConjCoord_TwoSquares
public import Definitions.Def_ConjCoord_Main
public import Theorems.Thm_ConjCoord_Proof_class_number_congruence

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof
namespace ConjCoord.Proof
theorem _root_.solution (S : SturmInput phi 512) {p : ℕ} (hp : p.Prime) (h5 : p % 16 = 5)
    {a b : ℤ} (hab : a ^ 2 + b ^ 2 = p) (hb : Even b) {h h' : ℕ}
    (hG : r3 p = 12 * h) (hG' : r3 (2 * p) = 12 * h') (V : Prop)
    (hV : V ↔ (h' : ℤ) - h ≡ 8 * (if p % 32 = 5 then 1 else 0) [ZMOD 16]) :
    V ↔ ((b % 16 = 6 ∨ b % 16 = 10) ↔ ¬ p % 32 = 21) := by
  have hc := class_number_congruence S hp h5 hab hb hG hG'
  rw [hV]
  unfold Int.ModEq at *
  unfold octA at hc
  have h32 : p % 32 = 5 ∨ p % 32 = 21 := by omega
  by_cases hA : b % 16 = 6 ∨ b % 16 = 10
  · rw [if_pos hA] at hc
    rcases h32 with h32 | h32
    · rw [if_pos h32]
      have e : ((b % 16 = 6 ∨ b % 16 = 10) ↔ ¬ p % 32 = 21) ↔ True := by
        rw [iff_true]; constructor <;> intro <;> omega
      rw [e, iff_true]; omega
    · rw [if_neg (by omega)]
      have e : ((b % 16 = 6 ∨ b % 16 = 10) ↔ ¬ p % 32 = 21) ↔ False := by
        rw [iff_false]; intro h; exact (h.mp hA) h32
      rw [e, iff_false]; omega
  · rw [if_neg hA] at hc
    rcases h32 with h32 | h32
    · rw [if_pos h32]
      have e : ((b % 16 = 6 ∨ b % 16 = 10) ↔ ¬ p % 32 = 21) ↔ False := by
        rw [iff_false]; intro h; exact hA (h.mpr (by omega))
      rw [e, iff_false]; omega
    · rw [if_neg (by omega)]
      have e : ((b % 16 = 6 ∨ b % 16 = 10) ↔ ¬ p % 32 = 21) ↔ True := by
        rw [iff_true]; constructor
        · intro h; exact absurd h hA
        · intro h; exact absurd h32 h
      rw [e, iff_true]; omega
end ConjCoord.Proof
