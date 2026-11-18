-- Prove2me | solution 1 for CallCountPOPBR.Supplement.theorem_7_8
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T15:23:55.58777+00:00
-- url     : https://prove2.me/submissions/4eee0c92-406c-459d-bcbe-343b43b898ae

import Mathlib
import Definitions.Def_CallCountPOPBR_Supplement_BinSpec

set_option autoImplicit false

namespace CC78Aux
open CallCountPOPBR.Supplement

lemma count_eq (s : BinSpec 1) (n : ℕ) :
    s.count n = if h : 1 ≤ n then
      1 + Sym2.lift ⟨fun i j : Fin n => s.count i + s.count j, fun _ _ => Nat.add_comm _ _⟩ (s n h)
    else 1 := by
  unfold BinSpec.count
  rw [Nat.strongRec_eq]

lemma count_zero (s : BinSpec 1) : s.count 0 = 1 := by
  rw [count_eq]; simp

lemma count_pair (s : BinSpec 1) (n : ℕ) (h : 1 ≤ n) (i j : Fin n) (hz : s n h = s(i, j)) :
    s.count n = 1 + s.count i + s.count j := by
  rw [count_eq, dif_pos h, hz, Sym2.lift_mk]; ring

end CC78Aux

open CallCountPOPBR.Supplement in
theorem solution (σ : BinSpec 1) :
    (∀ n, σ.count n = 2 ^ (n + 1) - 1) ↔
      ∀ n (h : 1 ≤ n), σ n h = s((⟨n - 1, by omega⟩ : Fin n), (⟨n - 1, by omega⟩ : Fin n)) := by
  constructor
  · intro hc n h
    obtain ⟨⟨i, j⟩, hz⟩ := Quot.exists_rep (σ n h)
    have hz' : σ n h = s(i, j) := hz.symm
    have e := CC78Aux.count_pair σ n h i j hz'
    rw [hc, hc, hc] at e
    have hi : 2 ^ (i.val + 1) ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hj : 2 ^ (j.val + 1) ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpi : 1 ≤ 2 ^ (i.val + 1) := Nat.one_le_two_pow
    have hpj : 1 ≤ 2 ^ (j.val + 1) := Nat.one_le_two_pow
    have hn2 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
    have ei : 2 ^ (i.val + 1) = 2 ^ n := by omega
    have ej : 2 ^ (j.val + 1) = 2 ^ n := by omega
    have ii : i.val + 1 = n := Nat.pow_right_injective (le_refl 2) ei
    have jj : j.val + 1 = n := Nat.pow_right_injective (le_refl 2) ej
    rw [hz']
    congr 1 <;> ext <;> simp <;> omega
  · intro hs n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [CC78Aux.count_zero]; norm_num
      · have e := CC78Aux.count_pair σ n hn _ _ (hs n hn)
        rw [e]
        simp only
        rw [ih (n - 1) (by omega)]
        have h1 : n - 1 + 1 = n := by omega
        rw [h1]
        have hp : 1 ≤ 2 ^ n := Nat.one_le_two_pow
        have hn2 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
        omega
