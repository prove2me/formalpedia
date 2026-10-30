-- Prove2me | solution 1 for BwSC.LowerBound.p59_first_term
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T02:58:43.443925+00:00
-- url     : https://prove2.me/submissions/90948f92-a337-41cb-8b48-18f84718f5dd

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


lemma rIdx_bounds {S K : ℕ} (hK : 1 < K) : (-1 : ℤ) ≤ rIdx S K ∧ rIdx S K ≤ (K : ℤ) - 2 := by
  unfold rIdx qIdx
  by_cases hS : S = 0
  · subst hS; simp; omega
  · rw [if_neg hS]
    have hdm := Nat.div_add_mod (S - 1) (K - 1)
    have hlt := Nat.mod_lt (S - 1) (by omega : K - 1 > 0)
    have hS1 : ((S - 1 : ℕ) : ℤ) = (S : ℤ) - 1 := by omega
    have hK1 : ((K - 1 : ℕ) : ℤ) = (K : ℤ) - 1 := by omega
    have e : (S : ℤ) - 1 - (((S - 1) / (K - 1) : ℕ) : ℤ) * ((K : ℤ) - 1) = (((S - 1) % (K - 1) : ℕ) : ℤ) := by
      rw [← hS1, ← hK1]; push_cast; zify at hdm; linarith
    rw [e]
    constructor
    · have : (0 : ℤ) ≤ (((S - 1) % (K - 1) : ℕ) : ℤ) := by positivity
      linarith
    · zify at hlt; push_cast at hlt ⊢; omega

end BwSC.LowerBound

open BwSC.LowerBound in
theorem solution_second {K S T : ℕ} (hK : 1 < K) (hT : 2 * K ≤ T)
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

open BwSC.LowerBound in
theorem solution {K S T : ℕ} (hK : 1 < K) (hT : 2 * K ≤ T)
    (hcase : Real.logb 2 (Real.logb 2 ((T : ℝ) / K)) < (qIdx S K : ℝ) + 2) :
    rateA K S T ≤ 9 * Real.sqrt ((K : ℝ) * T) := by
  obtain ⟨hL1, hL2⟩ := p59_case hK hT (qIdx S K) hcase
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hK2 : (2 : ℝ) ≤ K := by exact_mod_cast (by omega : 2 ≤ K)
  have hTK : (K : ℝ) ≤ T := by exact_mod_cast (by omega : K ≤ T)
  have hT0 : (0 : ℝ) < T := by linarith
  obtain ⟨ha0, ha1⟩ := aExp_sub_half (qIdx S K)
  set a := aExp (qIdx S K) with ha
  have ha_le : a ≤ 1 := by
    have : (2 : ℝ) ^ (-((qIdx S K : ℕ) : ℝ)) ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num); simp
    linarith
  have key : (a - 1 / 2) * Real.logb 2 ((T : ℝ) / K) ≤ 2 := by
    have hpow : (2 : ℝ) ^ (-((qIdx S K : ℕ) : ℝ)) / 2 * (2 : ℝ) ^ ((qIdx S K : ℝ) + 2) = 2 := by
      rw [div_mul_eq_mul_div, ← Real.rpow_add (by norm_num)]
      have : -((qIdx S K : ℝ)) + ((qIdx S K : ℝ) + 2) = 2 := by ring
      rw [this]; norm_num
    calc (a - 1 / 2) * Real.logb 2 ((T : ℝ) / K)
        ≤ (2 : ℝ) ^ (-((qIdx S K : ℕ) : ℝ)) / 2 * Real.logb 2 ((T : ℝ) / K) :=
          mul_le_mul_of_nonneg_right ha1 (by linarith)
      _ ≤ (2 : ℝ) ^ (-((qIdx S K : ℕ) : ℝ)) / 2 * (2 : ℝ) ^ ((qIdx S K : ℝ) + 2) :=
          mul_le_mul_of_nonneg_left hL2.le (by positivity)
      _ = 2 := hpow
  have hcore := p59_core hK0 hTK key
  obtain ⟨hr1, hr2⟩ := rIdx_bounds (S := S) hK
  set m : ℝ := (K : ℝ) - (rIdx S K : ℝ) with hm
  have hr1' : (-1 : ℝ) ≤ (rIdx S K : ℝ) := by exact_mod_cast hr1
  have hr2' : (rIdx S K : ℝ) ≤ (K : ℝ) - 2 := by exact_mod_cast hr2
  have hm0 : 0 ≤ m := by linarith
  have hmK : m ≤ 3 / 2 * K := by linarith
  have h1 : m ^ (2 - a) ≤ (3 / 2 * (K : ℝ)) ^ (2 - a) :=
    Real.rpow_le_rpow hm0 hmK (by linarith)
  have h2 : (3 / 2 * (K : ℝ)) ^ (2 - a) = (3 / 2 : ℝ) ^ (2 - a) * ((K : ℝ) * (K : ℝ) ^ (1 - a)) := by
    rw [Real.mul_rpow (by norm_num) hK0.le]
    congr 1
    rw [show (2 : ℝ) - a = 1 + (1 - a) by ring, Real.rpow_add hK0, Real.rpow_one]
  have h3 : (3 / 2 : ℝ) ^ (2 - a) ≤ (3 / 2 : ℝ) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h4 : (3 / 2 : ℝ) ^ (2 : ℝ) = 9 / 4 := by norm_num
  have hrate : rateA K S T = m ^ (2 - a) / K * (T : ℝ) ^ a := rfl
  rw [hrate]
  have hTa : 0 ≤ (T : ℝ) ^ a := by positivity
  have hKa : 0 ≤ (K : ℝ) ^ (1 - a) := by positivity
  have h5 : m ^ (2 - a) / K * (T : ℝ) ^ a ≤ (3 / 2 : ℝ) ^ (2 - a) * ((K : ℝ) ^ (1 - a) * (T : ℝ) ^ a) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hK0]
    calc m ^ (2 - a) * (T : ℝ) ^ a ≤ (3 / 2 * (K : ℝ)) ^ (2 - a) * (T : ℝ) ^ a :=
          mul_le_mul_of_nonneg_right h1 hTa
      _ = _ := by rw [h2]; ring
  have h6 : (2 : ℝ) ^ (2 : ℝ) = 4 := by norm_num
  rw [h6] at hcore
  have hpos : 0 ≤ (K : ℝ) ^ (1 - a) * (T : ℝ) ^ a := by positivity
  have h7 : (3 / 2 : ℝ) ^ (2 - a) * ((K : ℝ) ^ (1 - a) * (T : ℝ) ^ a) ≤
      9 / 4 * (4 * Real.sqrt ((K : ℝ) * T)) := by
    rw [← h4]
    exact mul_le_mul h3 hcore hpos (by positivity)
  linarith
