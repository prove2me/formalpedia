-- Prove2me | solution 1 for Erdos287.dense_endpoint_carry_core
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T11:26:55.681488+00:00
-- url     : https://prove2.me/submissions/f4ee591d-c4fe-4115-bda6-0ad8e4de374c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Erdos287_dense_high_prime_support
import Theorems.Thm_Erdos287_high_dyadic_layer_pairs
import Theorems.Thm_Erdos287_count_and_unit_gaps_lower_bound_from_first_denominator
import Theorems.Thm_Erdos287_dense_high_prime_power_core

open Finset

set_option autoImplicit false

theorem solution (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hgap : ∀ i, i + 1 < k → f (i + 1) - f i ≤ 2)
    (hlarge : 381185219244960776204622798194589878857417272332616682539469868641615417785666328820964948335432532885427126626573411739149117629379557737669727589422795325435 < f (k - 1))
    (hratio : 250 * f (k - 1) ≤ 739 * f 0)
    (hunit : f (k - 1) < 2 * ((Finset.range (k - 1)).filter
      (fun i => f (i + 1) - f i = 1)).card)
    (hruns :
      let D := (Finset.range k).image f
      let R := (Finset.Icc (f 0) (f (k - 1) + 1 - 8)).filter
        (fun x => ∀ i ∈ Finset.range 8, x + i ∈ D)
      f (k - 1) < 100 * R.card)
    (hcarry : ∀ j : ℕ, 1 ≤ j →
      let D := (Finset.range k).image f
      (f (k - 1) = 6 * 3 ^ j → 4 * 3 ^ j ∈ D ∧ 5 * 3 ^ j ∉ D) ∧
      (f (k - 1) = 15 * 5 ^ j →
        let T := (Finset.Icc 6 14).filter (fun c => c ≠ 10 ∧ c * 5 ^ j ∉ D)
        (∑ c ∈ T, 72072 / c) % 5 = 2 ∧ (∀ c, T = {c} → c = 6 ∨ c = 11)))
    (hneighbors : ∀ j : ℕ, 1 ≤ j → f (k - 1) = 6 * 3 ^ j →
      let D := (Finset.range k).image f
      let r := 3 ^ j
      (5 * r - 1) ∈ D ∧ (5 * r + 1) ∈ D ∧
        ∀ p a : ℕ, p.Prime → 1 ≤ a →
          2 * p ^ a ≠ 5 * r - 1 ∧ 2 * p ^ a ≠ 5 * r + 1) : False := by
  classical
  let m := f 0
  let M := f (k - 1)
  let D := (range k).image f
  have hk0 : 0 < k := by omega
  have hlast : k - 1 < k := by omega
  have hm : 0 < m := (hf1 0 hk0).pos
  have hD : D ⊆ Icc m M := by
    intro n hn
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hn
    have hi' := mem_range.mp hi
    apply mem_Icc.mpr
    constructor
    · by_cases hzero : i = 0
      · simp [hzero, m]
      · exact (hmono 0 i (by omega) hi').le
    · by_cases heq : i = k - 1
      · simp [heq, M]
      · exact (hmono i (k - 1) (by omega) hlast).le
  have hinj : Set.InjOn f (↑(range k) : Set ℕ) := by
    intro i hi j hj h
    have hi' := mem_range.mp (show i ∈ range k from hi)
    have hj' := mem_range.mp (show j ∈ range k from hj)
    rcases lt_trichotomy i j with hij | hij | hij
    · exact ((hmono i j hij hj').ne h).elim
    · exact hij
    · exact ((hmono j i hij hi').ne h.symm).elim
  have hsumD : ∑ n ∈ D, (1 : ℚ) / n = 1 := by
    rw [show D = (range k).image f by rfl, sum_image (fun _ hi _ hj h => hinj hi hj h)]
    exact hsum
  have hratio' : M < 3 * m := by
    change 250 * M ≤ 739 * m at hratio
    omega

  have hm14 : 14 ≤ m := by
    change 250 * M ≤ 739 * m at hratio
    have hnum : 382613443 < M := by have := hlarge; omega
    omega
  have hcard : D.card = k := by
    change ((range k).image f).card = k
    rw [card_image_of_injOn hinj, card_range]
  have hcap := (card_le_card hD).trans_eq (Nat.card_Icc m M)
  rw [hcard] at hcap
  have hsumcap : k + m ≤ M + 1 := by omega
  have hcount : (Real.exp 1 - 1) * ((m : ℝ) - 1) ≤ (k : ℝ) :=
    (Erdos287.count_and_unit_gaps_lower_bound_from_first_denominator
      k hk f (hf1 0 hk0) hmono hsum).1
  have hm14R : (14 : ℝ) ≤ m := by exact_mod_cast hm14
  have hcapR : (k : ℝ) + m ≤ (M : ℝ) + 1 := by exact_mod_cast hsumcap
  have hE : (27 / 10 : ℝ) ≤ Real.exp 1 :=
    le_of_lt (lt_trans (by norm_num) Real.exp_one_gt_d9)
  have hEterm := mul_le_mul_of_nonneg_right hE (show 0 ≤ (m : ℝ) - 1 by linarith)
  have hspread : 5 * m ≤ 2 * M := by
    exact_mod_cast (show (5 : ℝ) * m ≤ 2 * M by linarith only [hcount, hcapR, hm14R, hEterm])
  refine Erdos287.dense_high_prime_power_core k hk f hf1 hmono hsum hgap hlarge hratio hunit hruns
    hcarry hneighbors (fun p e hp he hb => ?_) ?_
  · exact Erdos287.dense_high_prime_support D m M p e hm hp he hD hsumD hratio' hspread hb
  · intro e he hMe
    exact Erdos287.high_dyadic_layer_pairs D m M e hm he hD hsumD hratio' hMe

