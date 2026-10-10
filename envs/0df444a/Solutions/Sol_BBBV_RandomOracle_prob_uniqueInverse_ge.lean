-- Prove2me | solution 1 for BBBV.RandomOracle.prob_uniqueInverse_ge
-- status  : ACCEPTED   (prove)
-- author  : @elem
-- created : 2026-10-10T01:06:08.632394+00:00
-- url     : https://prove2.me/submissions/16aad187-9864-40a6-a40a-d1882320c740

import Mathlib
import Definitions.Def_BBBV_RandomOracle_QueryModel

open BBBV.RandomOracle

/-- `(1 - 1/2^n)^{2^n - 1} ≥ 1/e`. -/
lemma exp_neg_one_le_bbbv (n : ℕ) :
    Real.exp (-1) ≤ (((2 : ℝ) ^ n - 1) / 2 ^ n) ^ (2 ^ n - 1) := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    norm_num
  · have h1 : (1 : ℕ) ≤ 2 ^ n := Nat.one_le_two_pow
    have h2 : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hpos
    set k : ℕ := 2 ^ n - 1 with hk
    have hk1 : 1 ≤ k := by omega
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hkpos : (0 : ℝ) < k := by linarith
    have hm : ((2 : ℝ) ^ n - 1) / 2 ^ n = (k : ℝ) / ((k : ℝ) + 1) := by
      have : ((2 : ℝ) ^ n) = (k : ℝ) + 1 := by
        rw [hk]; push_cast [Nat.cast_sub h1]; ring
      rw [this]; ring
    rw [hm]
    have hexp : Real.exp (-1 / k) ≤ (k : ℝ) / (k + 1) := by
      have hle : 1 / (k : ℝ) + 1 ≤ Real.exp (1 / k) := Real.add_one_le_exp _
      have hposa : (0 : ℝ) < 1 / k + 1 := by positivity
      calc Real.exp (-1 / k) = (Real.exp (1 / k))⁻¹ := by
            rw [← Real.exp_neg]; congr 1; ring
        _ ≤ (1 / (k : ℝ) + 1)⁻¹ := inv_anti₀ hposa hle
        _ = (k : ℝ) / (k + 1) := by field_simp; try ring
    calc Real.exp (-1) = Real.exp (-1 / k) ^ k := by
          rw [← Real.exp_nat_mul]; congr 1; field_simp; try ring
      _ ≤ ((k : ℝ) / (k + 1)) ^ k := pow_le_pow_left₀ (Real.exp_pos _).le hexp k

open Classical in
theorem solution {n : ℕ} :
    ((Finset.univ.filter fun A : Str n → Str n => UniqueInverse A).card : ℝ) /
        (Fintype.card (Str n → Str n) : ℝ) = (((2 : ℝ) ^ n - 1) / 2 ^ n) ^ (2 ^ n - 1) ∧
      Real.exp (-1) ≤ (((2 : ℝ) ^ n - 1) / 2 ^ n) ^ (2 ^ n - 1) := by
  refine ⟨?_, exp_neg_one_le_bbbv n⟩
  have hcardStr : Fintype.card (Str n) = 2 ^ n := by simp [Str]
  -- the piece of oracles whose unique preimage of `1ⁿ` is `x`
  set piece : Str n → Finset (Str n → Str n) := fun x =>
    Fintype.piFinset (fun y => if y = x then {ones n} else Finset.univ.erase (ones n)) with hpiece_def
  have hfilter : (Finset.univ.filter fun A : Str n → Str n => UniqueInverse A) =
      Finset.univ.biUnion piece := by
    ext A
    rw [Finset.mem_filter, Finset.mem_biUnion]
    simp only [Finset.mem_univ, true_and, hpiece_def, Fintype.mem_piFinset, UniqueInverse]
    constructor
    · rintro ⟨x, hx, huniq⟩
      refine ⟨x, fun y => ?_⟩
      by_cases hyx : y = x
      · subst hyx; simp [hx]
      · simp only [hyx, if_false, Finset.mem_erase, Finset.mem_univ, and_true, ne_eq]
        intro hy; exact hyx (huniq y hy)
    · rintro ⟨x, hx⟩
      refine ⟨x, ?_, ?_⟩
      · have := hx x; simpa using this
      · intro y hy
        by_contra hyx
        have := hx y
        simp [hyx] at this
        exact this hy
  have hdisj : ∀ x ∈ (Finset.univ : Finset (Str n)), ∀ x' ∈ (Finset.univ : Finset (Str n)),
      x ≠ x' → Disjoint (piece x) (piece x') := by
    intro x _ x' _ hxx'
    rw [Finset.disjoint_left]
    intro A hA hA'
    simp only [hpiece_def, Fintype.mem_piFinset] at hA hA'
    have h1 := hA x
    have h2 := hA' x
    simp only [if_true, Finset.mem_singleton] at h1
    simp only [hxx', if_false, Finset.mem_erase, Finset.mem_univ, and_true, ne_eq] at h2
    exact h2 h1
  have hpiece : ∀ x, (piece x).card = (2 ^ n - 1) ^ (2 ^ n - 1) := by
    intro x
    simp only [hpiece_def]
    rw [Fintype.card_piFinset, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x)]
    rw [if_pos rfl, Finset.card_singleton, one_mul]
    rw [Finset.prod_eq_pow_card (b := (Finset.univ.erase (ones n)).card)
      (fun i hi => by rw [if_neg (Finset.ne_of_mem_erase hi)])]
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcardStr,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcardStr]
  rw [hfilter, Finset.card_biUnion hdisj]
  simp only [hpiece, Finset.sum_const, Finset.card_univ, hcardStr, smul_eq_mul, Fintype.card_fun]
  have h1 : (1 : ℕ) ≤ 2 ^ n := Nat.one_le_two_pow
  set k : ℕ := 2 ^ n - 1 with hk
  have hk1 : 2 ^ n = k + 1 := by omega
  have hkR : (k : ℝ) = 2 ^ n - 1 := by
    rw [hk]; push_cast [Nat.cast_sub h1]; ring
  push_cast
  rw [hk1, pow_succ, div_pow, hkR]
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  field_simp
  try ring
