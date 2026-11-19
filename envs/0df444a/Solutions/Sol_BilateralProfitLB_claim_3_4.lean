-- Prove2me | solution 1 for BilateralProfitLB.claim_3_4
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-18T13:16:07.697584+00:00
-- url     : https://prove2.me/submissions/754e7922-8e9a-465e-8f54-f7f54c6c9a68

import Mathlib
import Definitions.Def_BilateralProfitLB_Construction
import Theorems.Thm_BilateralProfitLB_expected_profit_formula


section BundlePart000


namespace BilateralProfitLB

private theorem w_pos {K : ℕ} (hK : 0 < K) : 0 < w K := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  unfold w
  positivity

private theorem w_le_quarter {K : ℕ} (hK : 0 < K) : w K ≤ 1 / 4 := by
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  unfold w
  exact one_div_le_one_div_of_le (by norm_num) (by linarith)

private theorem cast_mul_w {K : ℕ} (hK : 0 < K) : (K : ℝ) * w K = 1 / 4 := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  unfold w
  field_simp

private theorem a_ge_quarter {K j : ℕ} (hj : 1 ≤ j) : 1 / 4 ≤ a K j := by
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hw : 0 ≤ w K := by unfold w; positivity
  unfold a
  linarith [mul_nonneg (sub_nonneg.mpr hjr) hw]

private theorem endpoint_le_half {K j : ℕ} (hK : 0 < K) (hj : j ≤ K) :
    a K j + w K ≤ 1 / 2 := by
  have hjr : (j : ℝ) ≤ K := by exact_mod_cast hj
  have hmul := mul_le_mul_of_nonneg_right hjr (w_pos hK).le
  unfold a
  linarith [cast_mul_w hK]

private theorem I_subset {K j : ℕ} (hj₁ : 1 ≤ j) (hj₂ : j ≤ K) :
    I K j ⊆ Set.Ioo (1 / 4 : ℝ) (1 / 2) := by
  have hK : 0 < K := lt_of_lt_of_le (by decide : 0 < 1) (hj₁.trans hj₂)
  intro q hq
  exact ⟨(a_ge_quarter hj₁).trans_lt hq.1, hq.2.trans_le (endpoint_le_half hK hj₂)⟩

private theorem qstar_mem {K j : ℕ} (hK : 0 < K) : qstar K j ∈ I K j := by
  have hw := w_pos hK
  change a K j < a K j + w K / 2 ∧ a K j + w K / 2 < a K j + w K
  exact ⟨by linarith, by linarith⟩

private theorem normalized_qstar {K j : ℕ} (hK : 0 < K) : (qstar K j - a K j) / w K = 1 / 2 := by
  unfold qstar
  apply (div_eq_iff (w_pos hK).ne').mpr
  ring

end BilateralProfitLB
end BundlePart000


section BundlePart001



namespace BilateralProfitLB

local notation "U01" => Set.Icc (0 : ℝ) 1
local notation "plateau" => Set.Icc (1 / 4 : ℝ) (1 / 2)

private theorem baseline_on_plateau {q : ℝ} (hq : q ∈ plateau) : S0 q = 1 / (48 * q ^ 2) := by
  rcases hq.1.eq_or_lt with rfl | hL
  · norm_num [S0]
  · rw [S0, if_neg hL.not_ge, if_pos hq.2]

private theorem baseline_plateau_profit {q : ℝ} (hq : q ∈ U01) :
    q ^ 2 / 4 * S0 q ≤ 1 / 192 ∧ (q ^ 2 / 4 * S0 q = 1 / 192 ↔ q ∈ plateau) := by
  have hq0 := hq.1
  by_cases hqL : q < 1 / 4
  · have hgap : 1 / 192 - q ^ 2 / 4 * S0 q = (q - 1 / 4) ^ 2 * (8 * q + 1) / 12 := by
      rw [S0, if_pos hqL.le]
      ring
    have hsquare : 0 < (q - 1 / 4) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hqL.ne)
    have hlt : q ^ 2 / 4 * S0 q < 1 / 192 := by
      apply sub_pos.mp
      rw [hgap]
      positivity
    exact ⟨hlt.le, iff_of_false hlt.ne (fun h => hqL.not_ge h.1)⟩
  by_cases hqR : 1 / 2 < q
  · have hqpos : 0 < q := by linarith
    have hnotL : ¬ q ≤ 1 / 4 := by linarith
    have hgap : 1 / 192 - q ^ 2 / 4 * S0 q = (q - 1 / 2) ^ 2 / 48 := by
      rw [S0, if_neg hnotL, if_neg hqR.not_ge]
      field_simp
      ring
    have hsquare : 0 < (q - 1 / 2) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hqR.ne')
    have hlt : q ^ 2 / 4 * S0 q < 1 / 192 := by
      apply sub_pos.mp
      rw [hgap]
      positivity
    exact ⟨hlt.le, iff_of_false hlt.ne (fun h => hqR.not_ge h.2)⟩
  have hqP : q ∈ plateau := ⟨le_of_not_gt hqL, le_of_not_gt hqR⟩
  have hqpos : 0 < q := (by norm_num : (0 : ℝ) < 1 / 4).trans_le hqP.1
  have hqeq : q ^ 2 / 4 * S0 q = 1 / 192 := by
    rw [baseline_on_plateau hqP]
    field_simp
    ring
  exact ⟨hqeq.le, iff_of_true hqeq hqP⟩

private theorem midpoint_gap {K j : ℕ} (hj₁ : 1 ≤ j) (hj₂ : j ≤ K) :
    Delta K ≤ qstar K j ^ 2 / 4 * S K j (qstar K j) - 1 / 192 := by
  have hK : 0 < K := by omega
  let q := qstar K j
  have hqI : q ∈ I K j := qstar_mem hK
  have hqP : q ∈ plateau := Set.mem_Icc_of_Ioo (I_subset hj₁ hj₂ hqI)
  have hquarter : (0 : ℝ) ≤ 1 / 4 := by norm_num
  have hqsqL := pow_le_pow_left₀ hquarter hqP.1 2
  have hqsqR := pow_le_pow_left₀ (hquarter.trans hqP.1) hqP.2 2
  have hwsq := pow_le_pow_left₀ (w_pos hK).le (w_le_quarter hK) 2
  have hrho : rho (1 / 2) = 1 := by norm_num [rho]
  have hY : Y K j q = 48 * q ^ 2 - w K ^ 2 / 2 := by
    unfold Y Y0
    rw [baseline_on_plateau hqP, one_div_one_div, normalized_qstar hK, hrho]
    ring
  have hYpos : 0 < Y K j q := by rw [hY]; linarith
  have hYtop : Y K j q ≤ 12 := by rw [hY]; linarith [sq_nonneg (w K)]
  have hSq : S K j q = 1 / Y K j q := by simp [S, hj₁, hj₂, hqI]
  change Delta K ≤ q ^ 2 / 4 * S K j q - 1 / 192
  calc
    Delta K = w K ^ 2 / (384 * 12) := rfl
    _ ≤ w K ^ 2 / (384 * Y K j q) := by
      apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left hYtop (by norm_num)
    _ = q ^ 2 / 4 * S K j q - 1 / 192 := by
      rw [hSq]
      field_simp
      linarith [hY]

private theorem claim_3_4_from_expected_profit (K : ℕ) (hK : 1 ≤ K) :
    ((∀ q ∈ U01, h K 0 q ≤ 1 / 192) ∧
        ∀ q ∈ U01, (h K 0 q = 1 / 192 ↔ q ∈ plateau)) ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ K →
        ∀ q ∈ U01, q ∉ I K j → Delta K ≤ h K j (qstar K j) - h K j q := by
  have formula (j : ℕ) (hj : j ≤ K) (q : ℝ) (hq : q ∈ U01) :
      h K j q = q ^ 2 / 4 * S K j q :=
    (expected_profit_formula K hK j hj 0 q (by norm_num) hq).2.2.1
  have h₀ (q : ℝ) (hq : q ∈ U01) : h K 0 q = q ^ 2 / 4 * S0 q := by
    rw [formula 0 (Nat.zero_le _) q hq]
    simp [S]
  constructor
  · exact ⟨fun q hq => h₀ q hq ▸ (baseline_plateau_profit hq).1,
      fun q hq => h₀ q hq ▸ (baseline_plateau_profit hq).2⟩
  · intro j hj₁ hj₂ q hq hqI
    have hS : S K j q = S0 q := by simp [S, hqI]
    have hcomp : h K j q ≤ 1 / 192 := by
      rw [formula j hj₂ q hq, hS]
      exact (baseline_plateau_profit hq).1
    have hinterior : qstar K j ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2) :=
      I_subset hj₁ hj₂ (qstar_mem hK)
    have hqstar : qstar K j ∈ U01 := ⟨by linarith [hinterior.1], by linarith [hinterior.2]⟩
    have hmid := midpoint_gap hj₁ hj₂
    rw [← formula j hj₂ (qstar K j) hqstar] at hmid
    linarith

end BilateralProfitLB
end BundlePart001

open BilateralProfitLB

theorem solution (K : ℕ) (hK : 1 ≤ K) :
    ((∀ q ∈ Set.Icc (0 : ℝ) 1, h K 0 q ≤ 1 / 192) ∧
        ∀ q ∈ Set.Icc (0 : ℝ) 1, (h K 0 q = 1 / 192 ↔ q ∈ Set.Icc (1 / 4 : ℝ) (1 / 2))) ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ K →
        ∀ q ∈ Set.Icc (0 : ℝ) 1, q ∉ I K j → Delta K ≤ h K j (qstar K j) - h K j q := by
  exact BilateralProfitLB.claim_3_4_from_expected_profit K hK
