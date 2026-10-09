-- Prove2me | solution 1 for BookProof.ChapterCoherentTemperature.thermalProb_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:34:18.855855+00:00
-- url     : https://prove2.me/submissions/c7f89b21-c876-42b0-81da-e640f5f43f7b

-- Generated from ChapterCoherentTemperature.lean — solution of BookProof.ChapterCoherentTemperature.thermalProb_second_moment
import Mathlib
import Definitions.Def_ChapterCoherentTemperature
import Theorems.Thm_BookProof_ChapterCoherentTemperature_nbar_add_one_pos
import Theorems.Thm_BookProof_ChapterCoherentTemperature_norm_thermalRatio_lt_one
import Theorems.Thm_BookProof_ChapterCoherentTemperature_one_sub_thermalRatio
open BookProof.ChapterCoherentTemperature



noncomputable section




variable {nbar : ℝ}

variable {nbar : ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (h : 0 ≤ nbar) :
    ∑' n : ℕ, (n : ℝ) ^ 2 * thermalProb nbar n = 2 * nbar ^ 2 + nbar := by

  set r := thermalRatio nbar with hrdef
  have hr : ‖r‖ < 1 := norm_thermalRatio_lt_one h
  have hpos := nbar_add_one_pos h
  -- summability of the three geometric families involved
  have s0 : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_norm_lt_one hr
  have s1 : Summable (fun n : ℕ => (n : ℝ) * r ^ n) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hr).summable
  have s2 : Summable (fun n : ℕ => ((n + 2).choose 2 : ℝ) * r ^ n) :=
    (hasSum_choose_mul_geometric_of_norm_lt_one 2 hr).summable
  -- `n² = 2·C(n+2,2) − 3n − 2`
  have hpoly : ∀ n : ℕ, (n : ℝ) ^ 2 * r ^ n
      = 2 * (((n + 2).choose 2 : ℝ) * r ^ n) - 3 * ((n : ℝ) * r ^ n) - 2 * r ^ n := by
    intro n
    have hc : ((n + 2).choose 2 : ℝ) = ((n : ℝ) ^ 2 + 3 * n + 2) / 2 := by
      have : (n + 2).choose 2 = (n + 2) * (n + 1) / 2 := by
        rw [Nat.choose_two_right]
        congr 1
      rw [this]
      have hdvd : 2 ∣ (n + 2) * (n + 1) := by
        rcases Nat.even_or_odd n with he | ho
        · obtain ⟨t, ht⟩ := he
          exact ⟨(t + 1) * (n + 1), by subst ht; ring⟩
        · obtain ⟨t, ht⟩ := ho
          exact ⟨(n + 2) * (t + 1), by subst ht; ring⟩
      obtain ⟨t, ht⟩ := hdvd
      rw [ht, Nat.mul_div_cancel_left _ (by norm_num)]
      have : ((n : ℝ) + 2) * ((n : ℝ) + 1) = 2 * (t : ℝ) := by
        exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) ht
      nlinarith [this]
    rw [hc]; ring
  have hsum : ∑' n : ℕ, (n : ℝ) ^ 2 * r ^ n
      = 2 * (1 / (1 - r) ^ 3) - 3 * (r / (1 - r) ^ 2) - 2 * (1 - r)⁻¹ := by
    rw [tsum_congr hpoly]
    rw [Summable.tsum_sub ((s2.mul_left 2).sub (s1.mul_left 3)) (s0.mul_left 2),
      Summable.tsum_sub (s2.mul_left 2) (s1.mul_left 3),
      s2.tsum_mul_left, s1.tsum_mul_left, s0.tsum_mul_left,
      tsum_choose_mul_geometric_of_norm_lt_one 2 hr,
      tsum_coe_mul_geometric_of_norm_lt_one hr,
      tsum_geometric_of_norm_lt_one hr]
  have hfinal : ∑' n : ℕ, (n : ℝ) ^ 2 * thermalProb nbar n
      = (1 / (nbar + 1)) * ∑' n : ℕ, (n : ℝ) ^ 2 * r ^ n := by
    rw [← tsum_mul_left]
    exact tsum_congr fun n => by simp only [thermalProb, ← hrdef]; ring
  have h1r : 1 - r = 1 / (nbar + 1) := one_sub_thermalRatio h
  rw [hfinal, hsum, h1r, hrdef, thermalRatio]
  field_simp
  ring
