-- Prove2me | solution 1 for BoundedEntropyGames.ConvRate.eq_17
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:35:45.118853+00:00
-- url     : https://prove2.me/submissions/a53d0d3e-e5a1-4782-aa8c-bb48c3ba0a66

import Mathlib
import Definitions.Def_BoundedEntropyGames_ConvRate_Setting
import Definitions.Def_BoundedEntropyGames_ConvRate_Proof

open BoundedEntropyGames.ConvRate in
theorem solution (n f : ℕ) (hf : 1 ≤ f) :
    (∀ i j : ℕ, i ≤ j → j < f → blockLen n f j ≤ blockLen n f i) ∧
    (∀ i < f, (n : ℝ) / f - 1 ≤ blockLen n f i) ∧
    ∑ i ∈ Finset.range f, blockLen n f i = n ∧
    (blockLen n f 0 : ℝ) ≤ (n : ℝ) / f + 1 := by
  have hdm := Nat.div_add_mod n f
  have hml := Nat.mod_lt n (show f > 0 by omega)
  have hfR : (0 : ℝ) < f := by exact_mod_cast (show 0 < f by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hij hj
    unfold blockLen
    split_ifs <;> omega
  · intro i hi
    unfold blockLen
    have h1 : ((n / f : ℕ) : ℝ) ≤ ((n / f + if i < n % f then 1 else 0 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_right _ _
    refine le_trans ?_ h1
    rw [div_sub_one hfR.ne', div_le_iff₀ hfR]
    have : (n : ℝ) = (f : ℝ) * ((n / f : ℕ) : ℝ) + ((n % f : ℕ) : ℝ) := by
      exact_mod_cast hdm.symm
    have h2 : ((n % f : ℕ) : ℝ) < f := by exact_mod_cast hml
    nlinarith
  · unfold blockLen
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
      Finset.sum_boole]
    have : (Finset.range f).filter (fun i => i < n % f) = Finset.range (n % f) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [this, Finset.card_range, Nat.cast_id]
    rw [mul_comm]
    exact (Nat.mul_comm _ _).symm ▸ hdm
  · unfold blockLen
    have h1 := Nat.cast_div_le (α := ℝ) (m := n) (n := f)
    have h2 : ((n / f + if 0 < n % f then 1 else 0 : ℕ) : ℝ) ≤ ((n / f : ℕ) : ℝ) + 1 := by
      split_ifs <;> push_cast <;> linarith
    linarith
