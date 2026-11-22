-- Prove2me | solution 1 for Egrs75.MoveDigits.staircase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:30:37.912815+00:00
-- url     : https://prove2.me/submissions/14ca31d9-c477-46fe-85af-11433be288a3

module
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Digits.Lemmas
public import Definitions.Def_LeanPool_Egrs75_MoveDigits
public import Theorems.Thm_Egrs75_RepairPaperfaithful_digitAt_add_low


set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.MoveDigits
open Nat
open Egrs75
open Egrs75.LeafInduction
open Egrs75.RepairDV
open Egrs75.RepairPaperfaithful
namespace Egrs75.MoveDigits
theorem _root_.solution {q : ℕ} (hq3 : 3 ≤ q) (hqo : Odd q) :
    ∀ i R : ℕ, 2 * R + 3 ≤ q ^ i →
      ∃ k, k < i ∧ R / q ^ k % q < (q - 1) / 2 ∧
        ∀ t, k < t → t < i → R / q ^ t % q = (q - 1) / 2 := by
  intro i
  induction i with
  | zero =>
    simp_all
  | succ i ih =>
    intro R hR
    have hq1 : 1 < q := by omega
    have hqi : 0 < q ^ i := pow_pos (by omega) i
    have hqs : q ^ (i + 1) = q ^ i * q := pow_succ q i
    have hB2 : 2 * ((q - 1) / 2) = q - 1 := by
      obtain ⟨c, hc⟩ := hqo; omega
    have hRlt : R < q ^ (i + 1) := by omega
    have hdlt : R / q ^ i < q := by
      rw [Nat.div_lt_iff_lt_mul hqi]
      have hcomm : q * q ^ i = q ^ i * q := Nat.mul_comm _ _
      omega
    have hdmod : R / q ^ i % q = R / q ^ i := Nat.mod_eq_of_lt hdlt
    rcases Nat.lt_trichotomy (R / q ^ i) ((q - 1) / 2) with hlt | heq | hgt
    · -- top digit of the window strictly good: it is the barrier.
      exact ⟨i, Nat.lt_succ_self i, by rw [hdmod]; exact hlt,
        fun t ht1 ht2 => by omega⟩
    · -- top digit exactly B: recurse into the low block.
      have hsplit : R = R % q ^ i + q ^ i * (R / q ^ i) :=
        (Nat.mod_add_div R (q ^ i)).symm
      have hlow2 : 2 * (R % q ^ i) + 3 ≤ q ^ i := by
        have h1 : q ^ i * (q - 1) + q ^ i = q ^ i * q := by
          have hq' : q - 1 + 1 = q := by omega
          calc q ^ i * (q - 1) + q ^ i = q ^ i * ((q - 1) + 1) := by ring
            _ = q ^ i * q := by rw [hq']
        have h2 : 2 * R = 2 * (R % q ^ i) + q ^ i * (q - 1) := by
          calc 2 * R = 2 * (R % q ^ i + q ^ i * (R / q ^ i)) := by
                conv_lhs => rw [hsplit]
            _ = 2 * (R % q ^ i) + q ^ i * (2 * (R / q ^ i)) := by ring
            _ = 2 * (R % q ^ i) + q ^ i * (2 * ((q - 1) / 2)) := by rw [heq]
            _ = 2 * (R % q ^ i) + q ^ i * (q - 1) := by rw [hB2]
        omega
      obtain ⟨k, hk, hkstrict, hkbet⟩ := ih (R % q ^ i) hlow2
      have hlowdig : ∀ t, t < i → R / q ^ t % q = (R % q ^ i) / q ^ t % q := by
        intro t ht
        have hlow := digitAt_add_low (p := q) (by omega) (k := i)
          (u := R % q ^ i) (h := R / q ^ i) (i := t) ht
        unfold digitAt at hlow
        calc R / q ^ t % q
            = (R % q ^ i + q ^ i * (R / q ^ i)) / q ^ t % q := by
              conv_lhs => rw [hsplit]
          _ = (R % q ^ i) / q ^ t % q := hlow
      refine ⟨k, by omega, ?_, ?_⟩
      · rw [hlowdig k hk]; exact hkstrict
      · intro t ht1 ht2
        rcases Nat.lt_or_ge t i with hti | hti
        · rw [hlowdig t hti]; exact hkbet t ht1 hti
        · have hteq : t = i := by omega
          subst hteq
          rw [hdmod]; exact heq
    · -- top digit > B: impossible below the all-B ceiling.
      exfalso
      have h1 : ((q - 1) / 2 + 1) * q ^ i ≤ R / q ^ i * q ^ i :=
        Nat.mul_le_mul_right _ (by omega)
      have h2 : R / q ^ i * q ^ i ≤ R := Nat.div_mul_le_self R (q ^ i)
      have h3 : 2 * (((q - 1) / 2 + 1) * q ^ i) = q ^ i * q + q ^ i := by
        calc 2 * (((q - 1) / 2 + 1) * q ^ i)
            = (2 * ((q - 1) / 2) + 2) * q ^ i := by ring
          _ = (q + 1) * q ^ i := by rw [hB2]; congr 1; omega
          _ = q ^ i * q + q ^ i := by ring
      omega
end Egrs75.MoveDigits
