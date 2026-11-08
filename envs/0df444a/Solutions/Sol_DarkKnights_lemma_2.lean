-- Prove2me | solution 1 for DarkKnights.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T01:40:09.115531+00:00
-- url     : https://prove2.me/submissions/72a8ea4c-f5e7-4551-b105-e8c3fbf46747

import Mathlib
import Definitions.Def_DarkKnights_Primitives
import Definitions.Def_DarkKnights_ActiveSellerModel

namespace Aux_DarkKnights_l2
open DarkKnights

theorem E_repay (a d r : ℝ) (h1 : d ≤ a) (h2 : r ≤ a → d ≤ r) : equityPayoff a d r = a - d := by
  unfold equityPayoff defaultAction
  rw [if_pos (⟨by linarith, fun h => by linarith [h2 h]⟩ : 0 ≤ a - d ∧ (r ≤ a → a - r ≤ a - d))]

theorem E_reneg (a d r : ℝ) (h1 : r ≤ a) (h2 : r < d) : equityPayoff a d r = a - r := by
  unfold equityPayoff defaultAction
  rw [if_neg (by rintro ⟨_, h⟩; linarith [h h1]), if_pos (⟨h1, by linarith⟩ : r ≤ a ∧ 0 ≤ a - r)]

theorem E_liq (a d r : ℝ) (h1 : a < r) (h2 : a < d) : equityPayoff a d r = 0 := by
  unfold equityPayoff defaultAction
  rw [if_neg (by rintro ⟨h, _⟩; linarith), if_neg (by rintro ⟨h, _⟩; linarith)]

theorem key (a b h bn θ : ℝ) (hacc : accepts a b h (bn, θ)) :
    dealerPayoff a b h (bn, θ) = θ * equityPayoff a bn (h * b) - (b - bn)
      - h * b * liqInd a bn (h * b) := by
  simp only [dealerPayoff, stake, faceValue, injection, if_pos hacc]

theorem acc_iff (a b h bn θ : ℝ) :
    accepts a b h (bn, θ) ↔ equityPayoff a b (h * b) ≤ (1 - θ) * equityPayoff a bn (h * b) :=
  Iff.rfl

end Aux_DarkKnights_l2

open DarkKnights Aux_DarkKnights_l2 in
theorem solution (a b bn h : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hbn : 0 ≤ bn) (hbnb : bn ≤ b)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    let θ : ℝ :=
      if bn ≤ h * b then (if h * b ≤ a then 1 - (a - h * b) / (a - bn) else 1)
      else (if h * b ≤ a then 0 else 1)
    θ ∈ Set.Icc (0 : ℝ) 1 ∧ accepts a b h (bn, θ) ∧
      ∀ θ' ∈ Set.Icc (0 : ℝ) 1, accepts a b h (bn, θ') →
        dealerPayoff a b h (bn, θ') ≤ dealerPayoff a b h (bn, θ) := by
  intro θ
  have hrb : h * b ≤ b := by nlinarith
  have hr0 : 0 ≤ h * b := mul_nonneg hh hb
  -- generic finishing step
  have fin : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → accepts a b h (bn, t) →
      (∀ θ' ∈ Set.Icc (0 : ℝ) 1, accepts a b h (bn, θ') →
        θ' * equityPayoff a bn (h * b) ≤ t * equityPayoff a bn (h * b)) →
      t ∈ Set.Icc (0 : ℝ) 1 ∧ accepts a b h (bn, t) ∧
        ∀ θ' ∈ Set.Icc (0 : ℝ) 1, accepts a b h (bn, θ') →
          dealerPayoff a b h (bn, θ') ≤ dealerPayoff a b h (bn, t) := by
    intro t ht hacc hmax
    refine ⟨ht, hacc, fun θ' hθ' hacc' => ?_⟩
    rw [key _ _ _ _ _ hacc', key _ _ _ _ _ hacc]
    linarith [hmax θ' hθ' hacc']
  have hEb : h * b ≤ a → equityPayoff a b (h * b) = a - h * b := by
    intro h2
    rcases eq_or_lt_of_le hrb with he | he
    · rw [E_repay a b (h * b) (by linarith) (fun _ => by linarith)]; linarith
    · exact E_reneg a b (h * b) h2 he
  by_cases h1 : bn ≤ h * b
  · by_cases h2 : h * b ≤ a
    · have hθ : θ = 1 - (a - h * b) / (a - bn) := by
        simp only [θ, if_pos h1, if_pos h2]
      rw [hθ]
      have hEn : equityPayoff a bn (h * b) = a - bn :=
        E_repay a bn (h * b) (by linarith) (fun _ => h1)
      have hθE : (1 - (a - h * b) / (a - bn)) * (a - bn) = (a - bn) - (a - h * b) := by
        rcases eq_or_lt_of_le (show 0 ≤ a - bn by linarith) with he | he
        · have : a - h * b = 0 := by linarith
          rw [← he, this]; ring
        · field_simp
      apply fin
      · constructor
        · have : (a - h * b) / (a - bn) ≤ 1 := div_le_one_of_le₀ (by linarith) (by linarith)
          linarith
        · have : 0 ≤ (a - h * b) / (a - bn) := div_nonneg (by linarith) (by linarith)
          linarith
      · rw [acc_iff, hEn, hEb h2]
        have e : (1 - (1 - (a - h * b) / (a - bn))) * (a - bn) =
            (a - bn) - (1 - (a - h * b) / (a - bn)) * (a - bn) := by ring
        rw [e, hθE]
        linarith
      · intro θ' _ hacc'
        rw [acc_iff, hEn, hEb h2] at hacc'
        rw [hEn, hθE]
        nlinarith
    · have hθ : θ = 1 := by simp only [θ, if_pos h1, if_neg h2]
      rw [hθ]
      push_neg at h2
      have hEb0 : equityPayoff a b (h * b) = 0 := E_liq a b (h * b) h2 (by linarith)
      have hEn0 : 0 ≤ equityPayoff a bn (h * b) := by
        by_cases h3 : bn ≤ a
        · rw [E_repay a bn (h * b) h3 (fun h4 => absurd h4 (not_le.mpr h2))]; linarith
        · rw [E_liq a bn (h * b) h2 (lt_of_not_ge h3)]
      apply fin
      · exact ⟨by norm_num, le_refl _⟩
      · rw [acc_iff, hEb0]; simp
      · intro θ' hθ' _
        nlinarith [hθ'.2]
  · push_neg at h1
    by_cases h2 : h * b ≤ a
    · have hθ : θ = 0 := by simp only [θ, if_neg (not_le.mpr h1), if_pos h2]
      rw [hθ]
      have hEn : equityPayoff a bn (h * b) = a - h * b := E_reneg a bn (h * b) h2 h1
      apply fin
      · exact ⟨le_refl _, by norm_num⟩
      · rw [acc_iff, hEn, hEb h2]; simp
      · intro θ' _ hacc'
        rw [acc_iff, hEn, hEb h2] at hacc'
        rw [hEn]
        nlinarith
    · have hθ : θ = 1 := by simp only [θ, if_neg (not_le.mpr h1), if_neg h2]
      rw [hθ]
      push_neg at h2
      have hEb0 : equityPayoff a b (h * b) = 0 := E_liq a b (h * b) h2 (by linarith)
      have hEn0 : equityPayoff a bn (h * b) = 0 := E_liq a bn (h * b) h2 (by linarith)
      apply fin
      · exact ⟨by norm_num, le_refl _⟩
      · rw [acc_iff, hEb0]; simp
      · intro θ' _ _
        rw [hEn0]; simp
