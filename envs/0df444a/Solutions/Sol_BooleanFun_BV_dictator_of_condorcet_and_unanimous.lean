-- Prove2me | solution 1 for BooleanFun.BV.dictator_of_condorcet_and_unanimous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:15:29.383728+00:00
-- url     : https://prove2.me/submissions/28581ce2-2754-4e97-b1c2-54168864924f

import Definitions.Def_BooleanFun_BooleanValued
import Definitions.Def_BooleanFun_Arrow
import Theorems.Thm_BooleanFun_BV_zero_not_unanimous
import Theorems.Thm_BooleanFun_BV_probabilityCondorcetWinner_eq_one
import Theorems.Thm_BooleanFun_BV_probabilityCondorcetWinner_eq
import Theorems.Thm_BooleanFun_BV_eq_character_of_fourier_weight_one_eq_one
import Theorems.Thm_BooleanFun_BV_fourier_eq_one
import Theorems.Thm_BooleanFun_BV_norm_sq_eq_one
import Theorems.Thm_BooleanFun_fourier_eq_zero_iff_fourier_weight_eq
import Theorems.Thm_BooleanFun_noise_stability_eq_sum_fourier
import Theorems.Thm_BooleanFun_pow_eq_self_imp


set_option autoImplicit false
noncomputable section
open BooleanFun BooleanFun.BV
open Classical Mathlib Finset Pi RealInnerProductSpace
variable {α : Type*} {ι : Type*}
variable {n : ℕ}
variable {f : BooleanFunc n}
local notation "T" => _Tnae3
namespace BooleanFun.BV
theorem _root_.solution (hbv : BooleanValued f)
    (hf : IsUnanimous f) (hf' : IsCondorcet f) : HasDictator f := by
  wlog hn : 0 < n
  · have := zero_not_unanimous f (Nat.eq_zero_of_not_pos hn)
    contradiction
  have := probabilityCondorcetWinner_eq_one hf'
  let ρ : ℝ := -1/3
  have : noise_stability ρ f = ρ := by
    rw [probabilityCondorcetWinner_eq hbv] at this
    calc
      _ = 1-4/3 * (3/4 * ((1 : ℝ)-(noise_stability ρ f))) := by ring
      _ = _   := by rw [this]; ring
  have hsumzero : ∑ S, (ρ^S.card - ρ) * |𝓕 f S|^2 = 0 := by
    simp_rw [sub_mul, sum_sub_distrib]
    rw [← noise_stability_eq_sum_fourier, this]
    nth_rewrite 1 [← mul_one ρ]
    rw [← fourier_eq_one hbv, mul_sum, sub_self]
  have hmz : ∀ S ∈ univ, (ρ^S.card - ρ) * |𝓕 f S|^2 = 0 := by {
    have : ∀ S ∈ univ, 0 ≤ (ρ ^ S.card - ρ) * |𝓕 f S| ^ 2 := by
      intro S _
      apply mul_nonneg
      · by_cases hk : Even S.card
        · obtain ⟨k, hk⟩ := hk
          rw [hk, ← two_mul]
          apply add_nonneg
          · calc
              0 ≤ (ρ^2)^k := pow_nonneg (pow_two_nonneg _) _
              _ = ρ^(2 * k) := by rw [pow_mul]
          · norm_num
        · obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp hk
          rw [hk]
          calc
            0 ≤ (-ρ) * (1-(ρ^2)^k)    := by
              apply mul_nonneg; norm_num; apply sub_nonneg.mpr;
              exact pow_le_one₀ (pow_two_nonneg ρ) (by norm_num)
            _ = (-ρ) * (1-ρ^(2 * k))    := by rw [pow_mul]
            _ = ρ^(2 * k + 1)-ρ         := by ring
      · exact sq_nonneg _
    apply (sum_eq_zero_iff_of_nonneg this).mp hsumzero
  }
  have hnez : ∀ k : ℕ, k ≠ 1 → ρ^k - ρ ≠ 0 := by
    intro k
    apply not_imp_not.mpr
    intro h
    have h := eq_add_of_sub_eq h
    rw [zero_add] at h
    obtain h|h|h|h := pow_eq_self_imp h
      <;> first | assumption | norm_num at h
  have : ∀ S, S.card ≠ 1 → 𝓕 f S = 0 := by
    intro S hS
    have := hmz S (by simp)
    have := eq_zero_of_ne_zero_of_mul_left_eq_zero (hnez S.card hS) this
    simp at this
    assumption
  have := fourier_eq_zero_iff_fourier_weight_eq.mp this
  rw [norm_sq_eq_one hbv] at this
  obtain ⟨i, ⟨c, hfeq⟩⟩ := eq_character_of_fourier_weight_one_eq_one hbv hn this
  use i
  have := funext_iff.mp hfeq 0
  rw [hf.1] at this
  simp at this
  rw [hfeq, ← this]
  simp
end BooleanFun.BV
