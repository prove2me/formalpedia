-- Prove2me | solution 1 for BwSC.LowerBound.p59_second_term
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T02:58:42.69052+00:00
-- url     : https://prove2.me/submissions/7eed0a5b-073d-42be-a471-e64360827ad3

import Mathlib
import Definitions.Def_BwSC_LowerBound_Model

open MeasureTheory ProbabilityTheory BanditAlgorithm
namespace BwSC.LowerBound

lemma p59_core {K T a c : ℝ} (hK : 0 < K) (hTK : K ≤ T)
    (h : (a - 1 / 2) * Real.logb 2 (T / K) ≤ c) :
    K ^ (1 - a) * T ^ a ≤ (2 : ℝ) ^ c * Real.sqrt (K * T) := by
  have hT : 0 < T := lt_of_lt_of_le hK hTK
  set x := T / K with hx
  have hx1 : 1 ≤ x := by rw [hx, le_div_iff₀ hK]; linarith
  have hx0 : 0 < x := by linarith
  have hTe : T = K * x := by rw [hx]; field_simp
  have e1 : K ^ (1 - a) * T ^ a = K * x ^ a := by
    rw [hTe, Real.mul_rpow hK.le hx0.le, Real.rpow_sub hK, Real.rpow_one]
    field_simp
  have e2 : Real.sqrt (K * T) = K * x ^ ((1:ℝ) / 2) := by
    rw [hTe, Real.sqrt_eq_rpow, ← mul_assoc, Real.mul_rpow (by positivity) hx0.le]
    congr 1
    rw [← Real.sqrt_eq_rpow, Real.sqrt_mul_self hK.le]
  have e3 : x ^ a = x ^ ((1:ℝ) / 2) * x ^ (a - 1 / 2) := by
    rw [← Real.rpow_add hx0]; congr 1; ring
  have e4 : x ^ (a - 1 / 2) = (2 : ℝ) ^ ((a - 1 / 2) * Real.logb 2 x) := by
    conv_lhs => rw [← Real.rpow_logb (by norm_num : (0:ℝ) < 2) (by norm_num) hx0]
    rw [← Real.rpow_mul (by norm_num)]
    ring_nf
  have e5 : x ^ (a - 1 / 2) ≤ (2 : ℝ) ^ c := by
    rw [e4]; exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h
  rw [e1, e2, e3]
  have : 0 ≤ K * x ^ ((1:ℝ) / 2) := by positivity
  nlinarith

/-- From the case hypothesis: `log₂ (T/K) < 2^(q+2)`, and `1 ≤ log₂ (T/K)`. -/
lemma p59_case {K T : ℕ} (hK : 1 < K) (hT : 2 * K ≤ T) (q : ℕ)
    (hcase : Real.logb 2 (Real.logb 2 ((T : ℝ) / K)) < (q : ℝ) + 2) :
    1 ≤ Real.logb 2 ((T : ℝ) / K) ∧ Real.logb 2 ((T : ℝ) / K) < (2 : ℝ) ^ ((q : ℝ) + 2) := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have h2 : (2 : ℝ) ≤ (T : ℝ) / K := by
    rw [le_div_iff₀ hK0]; exact_mod_cast (by omega : 2 * K ≤ T)
  have hL : 1 ≤ Real.logb 2 ((T : ℝ) / K) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]
    simpa using h2
  refine ⟨hL, ?_⟩
  exact (Real.logb_lt_iff_lt_rpow (by norm_num) (by linarith)).mp hcase

lemma aExp_sub_half (n : ℕ) :
    0 ≤ aExp n - 1 / 2 ∧ aExp n - 1 / 2 ≤ (2 : ℝ) ^ (-(n : ℝ)) / 2 := by
  set t := (2 : ℝ) ^ (-(n : ℝ)) with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 := by
    rw [ht]; apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num); simp
  have : aExp n = 1 / (2 - t) := rfl
  rw [this]
  have h2t : 0 < 2 - t := by linarith
  constructor
  · rw [sub_nonneg, div_le_div_iff₀ (by norm_num) h2t]; linarith
  · rw [div_sub_div _ _ h2t.ne' (by norm_num), div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith

end BwSC.LowerBound

open BwSC.LowerBound in
theorem solution {K S T : ℕ} (hK : 1 < K) (hT : 2 * K ≤ T)
    (hcase : Real.logb 2 (Real.logb 2 ((T : ℝ) / K)) < (qIdx S K : ℝ) + 2) :
    rateB K S T ≤ 2 * Real.sqrt ((K : ℝ) * T) := by
  obtain ⟨hL1, hL2⟩ := p59_case hK hT (qIdx S K) hcase
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hTK : (K : ℝ) ≤ T := by exact_mod_cast (by omega : K ≤ T)
  obtain ⟨ha0, ha1⟩ := aExp_sub_half (qIdx S K + 1)
  have key : (aExp (qIdx S K + 1) - 1 / 2) * Real.logb 2 ((T : ℝ) / K) ≤ 1 := by
    have hpow : (2 : ℝ) ^ (-(((qIdx S K + 1 : ℕ) : ℝ))) / 2 * (2 : ℝ) ^ ((qIdx S K : ℝ) + 2) = 1 := by
      rw [div_mul_eq_mul_div, ← Real.rpow_add (by norm_num)]
      push_cast
      have : -((qIdx S K : ℝ) + 1) + ((qIdx S K : ℝ) + 2) = 1 := by ring
      rw [this]; norm_num
    calc (aExp (qIdx S K + 1) - 1 / 2) * Real.logb 2 ((T : ℝ) / K)
        ≤ (2 : ℝ) ^ (-(((qIdx S K + 1 : ℕ) : ℝ))) / 2 * Real.logb 2 ((T : ℝ) / K) :=
          mul_le_mul_of_nonneg_right ha1 (by linarith)
      _ ≤ (2 : ℝ) ^ (-(((qIdx S K + 1 : ℕ) : ℝ))) / 2 * (2 : ℝ) ^ ((qIdx S K : ℝ) + 2) :=
          mul_le_mul_of_nonneg_left hL2.le (by positivity)
      _ = 1 := hpow
  have := p59_core hK0 hTK key
  simpa [rateB] using this
