-- Prove2me | solution 1 for FirstPriceLearning.ContextLowerBound.conclusion
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T05:59:07.598461+00:00
-- url     : https://prove2.me/submissions/1802512a-cb7a-4c2b-9b1f-801fa4b51cec

import Mathlib
import Definitions.Def_FirstPriceLearning_ContextLowerBound_Model
import Definitions.Def_FirstPriceLearning_ContextLowerBound_Construction
import Theorems.Thm_FirstPriceLearning_ContextLowerBound_eq_8

open MeasureTheory
open FirstPriceLearning.ContextLowerBound

theorem solution (M α T : ℕ) (hα : 1 ≤ α) (hM : 0 < M) (hK : ((α + 1) * M) ^ 3 ≤ T)
    (hMT : M ∣ T) {U : Type} [MeasurableSpace U] (μU : Measure U) [IsProbabilityMeasure μU]
    (π : Policy M (Act M α) U) :
    Real.sqrt ((((α + 1) * M : ℕ) : ℝ) * T) / (32 * Real.exp 3) ≤ maxRegret M α T hM μU π := by
  have hKT : (α + 1) * M ≤ T := by
    have h1 : 1 ≤ (α + 1) * M := Nat.one_le_iff_ne_zero.mpr (by positivity)
    calc (α + 1) * M = ((α + 1) * M) ^ 1 := (pow_one _).symm
      _ ≤ ((α + 1) * M) ^ 3 := Nat.pow_le_pow_right h1 (by norm_num)
      _ ≤ T := hK
  obtain ⟨h8a, h8b⟩ := eq_8 M α T hα hM hKT hMT μU π
  set R := maxRegret M α T hM μU π with hR
  set K : ℝ := (((α + 1) * M : ℕ) : ℝ) with hKdef
  have hKpos : 0 < K := by rw [hKdef]; exact_mod_cast (by positivity : 0 < (α + 1) * M)
  have hTpos : (0 : ℝ) < T := by
    have : 0 < (α + 1) * M := by positivity
    exact_mod_cast lt_of_lt_of_le this hKT
  have hK3 : K ^ 3 ≤ (T : ℝ) := by rw [hKdef]; exact_mod_cast hK
  set s := Real.sqrt (K * T) with hs
  have hs2 : s ^ 2 = K * T := Real.sq_sqrt (by positivity)
  have hspos : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hKs : K * s ≤ T := by
    have h : (K * s) ^ 2 ≤ (T : ℝ) ^ 2 := by
      rw [mul_pow, hs2]
      nlinarith [hK3, hKpos, hTpos]
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp h
  have he3 : 1 ≤ Real.exp 3 := Real.one_le_exp (by norm_num)
  have hmain : s / (16 * Real.exp 3) * Real.exp (-(16 * K * R / (3 * T))) ≤ R :=
    le_trans h8b h8a
  by_contra hcon
  push_neg at hcon
  -- x := 16 K R / (3T) < 1/6
  have hx : 16 * K * R / (3 * T) < 1 / 6 := by
    rw [div_lt_iff₀ (by positivity)]
    rcases le_or_gt R 0 with h | h
    · nlinarith
    · have h1 : R < s / 32 := by
        calc R < s / (32 * Real.exp 3) := hcon
          _ ≤ s / 32 := by
            apply div_le_div_of_nonneg_left hspos.le (by norm_num); nlinarith
      nlinarith
  have hexp : 1 / 2 < Real.exp (-(16 * K * R / (3 * T))) := by
    have := Real.add_one_le_exp (-(16 * K * R / (3 * T)))
    linarith
  have hB : 0 < s / (16 * Real.exp 3) := by positivity
  have : s / (16 * Real.exp 3) * (1 / 2) < R := by
    calc s / (16 * Real.exp 3) * (1 / 2) < s / (16 * Real.exp 3) * Real.exp (-(16 * K * R / (3 * T))) :=
          mul_lt_mul_of_pos_left hexp hB
      _ ≤ R := hmain
  have heq : s / (16 * Real.exp 3) * (1 / 2) = s / (32 * Real.exp 3) := by
    field_simp; ring
  linarith
