-- Prove2me | solution 1 for Champernowne.base_pow_countOccurrences_champPrefix_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:44:05.209706+00:00
-- url     : https://prove2.me/submissions/1c8719d5-406f-4101-8c1c-4bebd3dbad12

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Definitions.Def_LeanPool_Champernowne_Prefix
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Definitions.Def_LeanPool_Champernowne_Positions
public import Theorems.Thm_Champernowne_le_base_pow_countOccurrences_champPrefix
public import Theorems.Thm_Champernowne_card_allWords
public import Theorems.Thm_Champernowne_length_champPrefix
public import Theorems.Thm_Champernowne_mem_allWords
public import Theorems.Thm_Champernowne_sum_countOccurrences_allWords_le


set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution {b : ℕ} (hb : 1 < b) (n M : ℕ) {w : List ℕ}
    (hw : ∀ d ∈ w, d < b) (hwne : w ≠ []) (hM : 0 < M) (hwM : w.length ≤ M)
    (h1 : b ^ (M - 1) ≤ champIndex b n + 1) (h2 : champIndex b n + 1 ≤ b ^ M) :
    b ^ w.length * countOccurrences w (champPrefix b n)
      ≤ n + 7 * (w.length + 1) * b ^ (2 * w.length) * b ^ M := by
  have hk : 0 < w.length := List.length_pos_of_ne_nil hwne
  have hwW : w ∈ allWords b w.length := mem_allWords.mpr ⟨rfl, hw⟩
  -- Pigeonhole over all length-k words, with the w term split off.
  have hpig := sum_countOccurrences_allWords_le b w.length (champPrefix b n)
  rw [length_champPrefix, ← Finset.add_sum_erase _ _ hwW] at hpig
  have hpig' := Nat.mul_le_mul_left (b ^ w.length) hpig
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_one] at hpig'
  -- The lower transfer at each of the other words.
  have hlow : ∀ v ∈ (allWords b w.length).erase w,
      n ≤ b ^ w.length * countOccurrences v (champPrefix b n)
        + 7 * (w.length + 1) * b ^ w.length * b ^ M := by
    intro v hv
    obtain ⟨hvlen, hvlt⟩ := mem_allWords.mp (Finset.mem_of_mem_erase hv)
    have hvne : v ≠ [] := by
      intro hnil
      rw [hnil] at hvlen
      simp only [List.length_nil] at hvlen
      omega
    have hvM : v.length ≤ M := by rw [hvlen]; exact hwM
    have h := le_base_pow_countOccurrences_champPrefix hb n M hvlt hvne hM hvM h1 h2
    rwa [hvlen] at h
  have hsum := Finset.sum_le_sum hlow
  simp only [Finset.sum_const, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum] at hsum
  -- Count of the other words: card + 1 = b^k.
  have hcard : ((allWords b w.length).erase w).card + 1 = b ^ w.length := by
    rw [Finset.card_erase_of_mem hwW, card_allWords]
    have hp : 0 < b ^ w.length := pow_pos (by omega) _
    omega
  -- Rewrite the goal's error as b^k · (lower-bound error), then abstract.
  rw [show 7 * (w.length + 1) * b ^ (2 * w.length) * b ^ M
      = b ^ w.length * (7 * (w.length + 1) * b ^ w.length * b ^ M) by
    rw [two_mul, pow_add]; ring]
  set P := b ^ w.length with hPdef
  set E := 7 * (w.length + 1) * P * b ^ M with hEdef
  set C := countOccurrences w (champPrefix b n) with hCdef
  set S := ∑ v ∈ (allWords b w.length).erase w,
    countOccurrences v (champPrefix b n) with hSdef
  set c := ((allWords b w.length).erase w).card with hcdef
  -- Bridges between the omega atoms.
  have g1 : c * n + n = P * n := by rw [← hcard]; ring
  have g2 : c * E + E = P * E := by rw [← hcard]; ring
  have g3 : P ≤ E := by
    have hbM : 1 ≤ b ^ M := Nat.one_le_pow _ _ (by omega)
    calc P = 1 * P * 1 := by ring
    _ ≤ 7 * (w.length + 1) * P * b ^ M :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ (by omega)) hbM
  -- hpig' : P*C + P*S ≤ P*n + P; hsum : c*n ≤ P*S + c*E; goal : P*C ≤ n + P*E.
  omega
end Champernowne
