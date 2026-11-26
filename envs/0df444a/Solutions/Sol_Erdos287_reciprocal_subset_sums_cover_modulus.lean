-- Prove2me | solution 1 for Erdos287.reciprocal_subset_sums_cover_modulus
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T13:10:48.015897+00:00
-- url     : https://prove2.me/submissions/c9d4e8ec-94a2-4c10-8d7b-2ec9a724aff0

import Mathlib
import Theorems.Thm_Erdos287_additive_character_arc_contraction
import Theorems.Thm_Erdos287_additive_character_subset_sum_coverage
import Theorems.Thm_Erdos287_short_inverse_frequencies_have_few_large_prime_labels

open Finset

set_option autoImplicit false

/-- A set of modular reciprocal weights with distinct large prime labels
covers all residues once the exponential bound for its nonzero frequencies
is small enough. -/
theorem solution (q : ℕ) [NeZero q] (D : Finset ℕ) (label : ℕ → ℕ)
    (M R Y K : ℕ) (t : ZMod q) (hY : 2 ≤ Y)
    (hD : ∀ n ∈ D, n ≤ M ∧ (label n).Prime ∧ Y ≤ label n ∧ label n ∣ n)
    (hinj : Set.InjOn label (↑D : Set ℕ))
    (hunit : ∀ n ∈ D, IsUnit (n : ZMod q))
    (hsize : (M * R / q + 1) * q < Y ^ (K + 1))
    (hsmall : (q : ℝ) * Real.exp
      (-2 * ((R : ℝ) / q) ^ 2 * ↑(D.card - 2 * (M * R / q + 1) * K)) < 1) :
    ∃ T ⊆ D, (∑ n ∈ T, (n : ZMod q)⁻¹) = t := by
  classical
  let E := D.card - 2 * (M * R / q + 1) * K
  let η := 2 * ((R : ℝ) / q) ^ 2
  let W (a : ZMod q) (n : ℕ) := 1 + ZMod.stdAddChar (a * (n : ZMod q)⁻¹)
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hq : 0 < (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hbound (a : ZMod q) (ha : a ≠ 0) :
      ‖∏ n ∈ D, W a n‖ ≤ (2 : ℝ) ^ D.card * Real.exp (-η * E) := by
    let x (n : ℕ) := a * (n : ZMod q)⁻¹
    let C := D.filter (fun n => min (x n).val (q - (x n).val) ≤ R)
    have hCsub : C ⊆ D := filter_subset _ _
    have hC : C.card ≤ 2 * (M * R / q + 1) * K := by
      apply Erdos287.short_inverse_frequencies_have_few_large_prime_labels
        C label M q a.val R Y K _ (ZMod.val_lt a) hY
        (fun n hn => hD n (hCsub hn)) (hinj.mono hCsub) _ hsize
      · exact Nat.pos_of_ne_zero fun he => ha ((ZMod.val_eq_zero a).mp he)
      · intro n hn
        have hx : (n : ZMod q) * x n = a := by
          dsimp [x]
          rw [mul_left_comm, ZMod.mul_inv_of_unit _ (hunit n (hCsub hn)), mul_one]
        rcases min_le_iff.mp (mem_filter.mp hn).2 with h | h
        · refine ⟨(x n).val, h, Or.inl ?_⟩
          apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
          simpa only [Nat.cast_mul, ZMod.natCast_zmod_val] using hx
        · refine ⟨q - (x n).val, h, Or.inr ?_⟩
          apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
          simp only [Nat.cast_mul, Nat.cast_sub (ZMod.val_lt (x n)).le,
            Nat.cast_sub (ZMod.val_lt a).le, ZMod.natCast_self, ZMod.natCast_zmod_val,
            zero_sub, mul_neg, hx]
    have hfar : E ≤ (D \ C).card := by
      rw [card_sdiff_of_subset hCsub]
      exact Nat.sub_le_sub_left hC _
    have hnear (n : ℕ) : ‖W a n‖ ≤ 2 := by
      refine (norm_add_le _ _).trans_eq ?_
      simp [ZMod.stdAddChar_apply, Circle.norm_coe, one_add_one_eq_two]
    have hfarFactor (n : ℕ) (hn : n ∈ D \ C) : ‖W a n‖ ≤ 2 * Real.exp (-η) := by
      obtain ⟨hnD, hnC⟩ := mem_sdiff.mp hn
      have hr : R < min (x n).val (q - (x n).val) := by
        exact lt_of_not_ge fun he => hnC (mem_filter.mpr ⟨hnD, he⟩)
      have h₁ : (R : ℝ) ≤ (x n).val := by exact_mod_cast (lt_min_iff.mp hr).1.le
      have h₂ : (R : ℝ) ≤ (q : ℝ) - (x n).val := by
        have h : (R : ℝ) ≤ ↑(q - (x n).val) := by exact_mod_cast (lt_min_iff.mp hr).2.le
        simpa only [Nat.cast_sub (ZMod.val_lt (x n)).le] using h
      have hdist : (R : ℝ) / q ≤ min ((x n).val / (q : ℝ)) (1 - (x n).val / (q : ℝ)) := by
        apply le_min ((div_le_div_iff_of_pos_right hq).mpr h₁)
        simpa only [sub_div, div_self hq.ne'] using (div_le_div_iff_of_pos_right hq).mpr h₂
      refine (Erdos287.additive_character_arc_contraction q (x n)).trans ?_
      have hpos : 0 ≤ (R : ℝ) / q := by positivity
      have hs := (sq_le_sq₀ hpos (hpos.trans hdist)).mpr hdist
      gcongr
      dsimp [η]
      linarith
    calc
      ‖∏ n ∈ D, W a n‖ = (∏ n ∈ D \ C, ‖W a n‖) * ∏ n ∈ C, ‖W a n‖ := by
        rw [norm_prod, prod_sdiff hCsub]
      _ ≤ (∏ _ ∈ D \ C, 2 * Real.exp (-η)) * ∏ _ ∈ C, (2 : ℝ) := by
        exact mul_le_mul
          (prod_le_prod (fun _ _ => norm_nonneg _) hfarFactor)
          (prod_le_prod (fun _ _ => norm_nonneg _) (fun n _ => hnear n))
          (by positivity) (by positivity)
      _ = (2 : ℝ) ^ D.card * Real.exp (-η * ((D \ C).card : ℝ)) := by
        simp only [prod_const, mul_pow, ← Real.exp_nat_mul]
        rw [mul_right_comm, ← pow_add, card_sdiff_add_card_eq_card hCsub]
        congr 1
        ring
      _ ≤ _ := by
        have hc : (E : ℝ) ≤ ((D \ C).card : ℝ) := by exact_mod_cast hfar
        exact mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hc (neg_nonpos.mpr hη)))
          (by positivity)
  apply Erdos287.additive_character_subset_sum_coverage q D (fun n => (n : ZMod q)⁻¹) t
  change (∑ a ∈ univ.erase (0 : ZMod q), ‖∏ n ∈ D, W a n‖) < _
  have hcard : ((univ.erase (0 : ZMod q)).card : ℝ) ≤ q := by
    exact_mod_cast (show (univ.erase (0 : ZMod q)).card ≤ q from calc
      _ ≤ (univ : Finset (ZMod q)).card := card_le_card (erase_subset _ _)
      _ = Fintype.card (ZMod q) := card_univ
      _ = q := ZMod.card q)
  calc
    _ ≤ ∑ _ ∈ univ.erase (0 : ZMod q), (2 : ℝ) ^ D.card * Real.exp (-η * E) :=
      sum_le_sum fun a ha => hbound a (mem_erase.mp ha).1
    _ ≤ (2 : ℝ) ^ D.card * ((q : ℝ) * Real.exp (-η * E)) := by
      rw [sum_const, nsmul_eq_mul]
      calc
        _ ≤ (q : ℝ) * ((2 : ℝ) ^ D.card * Real.exp (-η * E)) := by gcongr
        _ = _ := by ring
    _ < _ := by
      simpa using mul_lt_mul_of_pos_left hsmall (pow_pos (by norm_num : (0 : ℝ) < 2) D.card)

