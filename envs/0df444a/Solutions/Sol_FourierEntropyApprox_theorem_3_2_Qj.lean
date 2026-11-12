-- Prove2me | solution 1 for FourierEntropyApprox.theorem_3_2_Qj
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T23:04:07.084691+00:00
-- url     : https://prove2.me/submissions/f9bb1f13-cce0-4c74-9b0e-910119e33a8e

import Mathlib
import Definitions.Def_FourierEntropyApprox_IsBoolean
import Definitions.Def_FourierEntropyApprox_majCompose
import Theorems.Thm_FourierEntropyApprox_theorem_3_2_item_1
import Theorems.Thm_FourierEntropyApprox_theorem_3_2_item_2

section
set_option autoImplicit false
namespace FourierEntropyApprox.Dev.Qj

lemma exp_bound (j : ℕ) : 4 * Real.exp (-(((4 * j + 8 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ 2)) ≤ ((2 : ℝ) ^ j)⁻¹ := by
  have h1 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  have h2 : (2 : ℝ) ^ (j + 2) ≤ Real.exp ((j + 2 : ℕ) : ℝ) := by
    rw [← Real.exp_one_pow]
    exact pow_le_pow_left₀ (by norm_num) h1 _
  have h3 : -(((4 * j + 8 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ 2) = -((j + 2 : ℕ) : ℝ) := by
    push_cast; ring
  rw [h3, Real.exp_neg]
  have hpos : (0 : ℝ) < 2 ^ j := by positivity
  have hE : 0 < Real.exp ((j + 2 : ℕ) : ℝ) := Real.exp_pos _
  rw [← div_eq_mul_inv, div_le_iff₀ hE, inv_mul_eq_div, le_div_iff₀ hpos]
  have : (2 : ℝ) ^ (j + 2) = 4 * 2 ^ j := by ring
  nlinarith

lemma pt_bounds (n : ℕ) (f P' : Cube n → ℝ) (hf : IsBoolean f) (h : ∀ x, |P' x - f x| ≤ 1 / 3)
    (x : Cube n) : |3 * P' x / 4| ≤ 1 ∧ (1 / 2 : ℝ) ≤ f x * (3 * P' x / 4) := by
  have hx := abs_le.mp (h x)
  rcases hf x with e | e <;> rw [e] at hx ⊢ <;> obtain ⟨a, b⟩ := hx
  · constructor
    · rw [abs_le]; constructor <;> linarith
    · linarith
  · constructor
    · rw [abs_le]; constructor <;> linarith
    · linarith

end FourierEntropyApprox.Dev.Qj
namespace FourierEntropyApprox
open FourierEntropyApprox.Dev.Qj in
theorem chk_theorem_3_2_Qj :
    ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ) (f P' : Cube n → ℝ), IsBoolean f → (∀ x, |P' x - f x| ≤ 1 / 3) →
      ∀ j : ℕ, 1 ≤ j →
        l2NormSq (f - majCompose (4 * j + 8) (fun x => 3 * P' x / 4)) ≤ ((2 : ℝ) ^ j)⁻¹ ∧
          Real.logb 2 (max 1 (spectralNorm (majCompose (4 * j + 8) (fun x => 3 * P' x / 4)))) ≤
            c * j * Real.logb 2 (1 + spectralNorm (fun x => 3 * P' x / 4)) := by
  refine ⟨12, by norm_num, ?_⟩
  intro n f P' hf h j hj
  constructor
  · have := (theorem_3_2_item_1 f (fun x => 3 * P' x / 4) (1 / 2) hf (by norm_num)
      (fun x => (pt_bounds n f P' hf h x).1) (fun x => (pt_bounds n f P' hf h x).2) (4 * j + 8)).2
    exact this.trans (exp_bound j)
  · set P : Cube n → ℝ := fun x => 3 * P' x / 4 with hPdef
    set B := spectralNorm P with hB
    have hB0 : 0 ≤ B := Finset.sum_nonneg fun S _ => norm_nonneg _
    have h2 := theorem_3_2_item_2 P (4 * j + 8)
    set R : ℝ := (1 + B ^ 2) ^ (((4 * j + 8 : ℕ) : ℝ) / 2) with hR
    have hR1 : 1 ≤ R := Real.one_le_rpow (by nlinarith) (by positivity)
    have hmax : max 1 (spectralNorm (majCompose (4 * j + 8) P)) ≤ R := max_le hR1 h2
    have hL0 : 0 ≤ Real.logb 2 (1 + B) := Real.logb_nonneg (by norm_num) (by linarith)
    calc Real.logb 2 (max 1 (spectralNorm (majCompose (4 * j + 8) P)))
        ≤ Real.logb 2 R := Real.logb_le_logb_of_le (by norm_num) (by positivity) hmax
      _ = (((4 * j + 8 : ℕ) : ℝ) / 2) * Real.logb 2 (1 + B ^ 2) := by
          rw [hR, Real.logb_rpow_eq_mul_logb_of_pos (by positivity)]
      _ ≤ (((4 * j + 8 : ℕ) : ℝ) / 2) * (2 * Real.logb 2 (1 + B)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have : Real.logb 2 (1 + B ^ 2) ≤ Real.logb 2 ((1 + B) ^ 2) :=
            Real.logb_le_logb_of_le (by norm_num) (by positivity) (by nlinarith)
          rwa [Real.logb_pow, Nat.cast_ofNat] at this
      _ ≤ 12 * j * Real.logb 2 (1 + B) := by
          have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
          push_cast
          nlinarith
end FourierEntropyApprox
end

theorem solution : type_of% @FourierEntropyApprox.chk_theorem_3_2_Qj := @FourierEntropyApprox.chk_theorem_3_2_Qj
