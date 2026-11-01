-- Prove2me | solution 1 for FBMStrongSim.RecordBreak.sup_norm_eq_max_disp
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T20:35:10.165417+00:00
-- url     : https://prove2.me/submissions/a1b7a449-2a45-42de-b4b5-312d5dd937ed

import Mathlib
import Definitions.Def_FBMStrongSim_RecordBreak_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FBMSupNormAux
open FBMStrongSim.RecordBreak

theorem interp_eq (x : ℝ → ℝ) (n : ℕ) (t : ℝ) (i : ℕ)
    (hi : i = min ⌊(2 : ℝ) ^ n * t⌋₊ (2 ^ n - 1)) :
    interp x n t = x (dyadic n i) + ((2 : ℝ) ^ n * t - i) * (x (dyadic n (i + 1)) - x (dyadic n i)) := by
  subst hi; rfl

theorem idx_facts (n : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ((min ⌊(2 : ℝ) ^ n * t⌋₊ (2 ^ n - 1) : ℕ) : ℝ) ≤ 2 ^ n * t ∧
    2 ^ n * t - ((min ⌊(2 : ℝ) ^ n * t⌋₊ (2 ^ n - 1) : ℕ) : ℝ) ≤ 1 ∧
    min ⌊(2 : ℝ) ^ n * t⌋₊ (2 ^ n - 1) + 1 ≤ 2 ^ n := by
  have h2m : (0 : ℝ) < 2 ^ n := by positivity
  set F : ℕ := ⌊(2 : ℝ) ^ n * t⌋₊ with hF
  have hs0 : 0 ≤ (2 : ℝ) ^ n * t := mul_nonneg h2m.le ht.1
  have hFle : (F : ℝ) ≤ 2 ^ n * t := Nat.floor_le hs0
  have hFlt : 2 ^ n * t < (F : ℝ) + 1 := Nat.lt_floor_add_one _
  have hcast : ((2 ^ n - 1 : ℕ) : ℝ) = 2 ^ n - 1 := by
    rw [Nat.cast_sub (Nat.one_le_two_pow)]; push_cast; ring
  have hp : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  refine ⟨?_, ?_, ?_⟩
  · exact le_trans (by exact_mod_cast min_le_left _ _) hFle
  · rcases le_total F (2 ^ n - 1) with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h, hcast]
      have : t ≤ 1 := ht.2
      nlinarith
  · have := min_le_right F (2 ^ n - 1)
    omega

theorem dy1 (m j : ℕ) : dyadic (m + 1) (2 * j) = dyadic m j := by
  unfold dyadic; push_cast; rw [pow_succ]; field_simp

theorem dy2 (m j : ℕ) : dyadic (m + 1) (2 * j + 1 + 1) = dyadic m (j + 1) := by
  unfold dyadic; push_cast; rw [pow_succ]; field_simp; ring

theorem idx_half (m : ℕ) (t : ℝ) :
    min ⌊(2 : ℝ) ^ (m + 1) * t⌋₊ (2 ^ (m + 1) - 1) / 2 = min ⌊(2 : ℝ) ^ m * t⌋₊ (2 ^ m - 1) := by
  have h1 : ⌊(2 : ℝ) ^ m * t⌋₊ = ⌊(2 : ℝ) ^ (m + 1) * t⌋₊ / 2 := by
    have := Nat.floor_div_natCast ((2 : ℝ) ^ (m + 1) * t) 2
    rw [← this]; congr 1; push_cast; rw [pow_succ]; ring
  have h2 : (2 ^ (m + 1) - 1) / 2 = 2 ^ m - 1 := by
    have hp : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    rw [pow_succ]; omega
  rw [h1, ← h2]
  rcases le_total ⌊(2 : ℝ) ^ (m + 1) * t⌋₊ (2 ^ (m + 1) - 1) with h | h
  · rw [min_eq_left h, min_eq_left (Nat.div_le_div_right h)]
  · rw [min_eq_right h, min_eq_right (Nat.div_le_div_right h)]

end FBMSupNormAux

open FBMStrongSim.RecordBreak FBMSupNormAux

theorem solution (x : ℝ → ℝ) (k : ℕ) (hk : 1 ≤ k) :
    IsGreatest ((fun t => |interp x k t - interp x (k - 1) t|) '' Set.Icc (0 : ℝ) 1)
      (maxDisp x k) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hne : (Finset.range (2 ^ (m + 1 - 1))).Nonempty := by simp
  have hmax : maxDisp x (m + 1) = (Finset.range (2 ^ (m + 1 - 1))).sup' hne
      (fun j => |disp x (m + 1) j|) := rfl
  have hdisp : ∀ j, disp x (m + 1) j =
      x (dyadic (m + 1) (2 * j + 1)) - (x (dyadic m j) + x (dyadic m (j + 1))) / 2 := by
    intro j; simp [disp]
  simp only [Nat.add_sub_cancel] at hne hmax ⊢
  constructor
  · obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup' hne (fun j => |disp x (m + 1) j|)
    have hjlt : j < 2 ^ m := Finset.mem_range.1 hj
    refine ⟨dyadic (m + 1) (2 * j + 1), ?_, ?_⟩
    · unfold dyadic
      have : (2 * j + 1 : ℕ) + 1 ≤ 2 ^ (m + 1) := by rw [pow_succ]; omega
      have h' : ((2 * j + 1 : ℕ) : ℝ) + 1 ≤ 2 ^ (m + 1) := by exact_mod_cast this
      constructor
      · positivity
      · rw [div_le_one (by positivity)]; linarith
    · have ht1 : (2 : ℝ) ^ (m + 1) * dyadic (m + 1) (2 * j + 1) = ((2 * j + 1 : ℕ) : ℝ) := by
        unfold dyadic; field_simp
      have hi1 : 2 * j + 1 = min ⌊(2 : ℝ) ^ (m + 1) * dyadic (m + 1) (2 * j + 1)⌋₊
          (2 ^ (m + 1) - 1) := by
        rw [ht1, Nat.floor_natCast]
        have : 2 * j + 1 ≤ 2 ^ (m + 1) - 1 := by rw [pow_succ]; omega
        rw [min_eq_left this]
      have ht2 : (2 : ℝ) ^ m * dyadic (m + 1) (2 * j + 1) = (j : ℝ) + 1 / 2 := by
        unfold dyadic; rw [pow_succ]; push_cast; field_simp
      have hi2 : j = min ⌊(2 : ℝ) ^ m * dyadic (m + 1) (2 * j + 1)⌋₊ (2 ^ m - 1) := by
        rw [ht2]
        have hfl : ⌊(j : ℝ) + 1 / 2⌋₊ = j := by
          rw [Nat.floor_eq_iff (by positivity)]; constructor <;> linarith
        rw [hfl, min_eq_left (by omega)]
      beta_reduce
      rw [interp_eq x (m + 1) _ _ hi1, interp_eq x m _ _ hi2, ht1, ht2]
      show _ = maxDisp x (m + 1)
      rw [hmax, hjeq, hdisp]
      congr 1
      ring
  · rintro _ ⟨t, ht, rfl⟩
    obtain ⟨f1, f2, f3⟩ := idx_facts (m + 1) t ht
    set i : ℕ := min ⌊(2 : ℝ) ^ (m + 1) * t⌋₊ (2 ^ (m + 1) - 1) with hi
    have hhalf := idx_half m t
    rw [← hi] at hhalf
    set j : ℕ := i / 2 with hj
    have hjlt : j < 2 ^ m := by
      have : i + 1 ≤ 2 * 2 ^ m := by rw [← pow_succ']; exact f3
      omega
    have hjmem : j ∈ Finset.range (2 ^ m) := Finset.mem_range.2 hjlt
    have hdle : |disp x (m + 1) j| ≤ maxDisp x (m + 1) := by
      rw [hmax]; exact Finset.le_sup' (fun j => |disp x (m + 1) j|) hjmem
    have hpow : (2 : ℝ) ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
    beta_reduce
    rw [interp_eq x (m + 1) t i hi, interp_eq x m t j hhalf]
    show _ ≤ maxDisp x (m + 1)
    rcases Nat.even_or_odd' i with ⟨j', hj' | hj'⟩
    · have hjj : j = j' := by rw [hj, hj']; omega
      rw [← hjj] at hj'
      rw [hj', dy1]
      set lam : ℝ := 2 ^ (m + 1) * t - ((2 * j : ℕ) : ℝ) with hlam
      have hl0 : 0 ≤ lam := by rw [hlam, ← hj']; linarith
      have hl1 : lam ≤ 1 := by rw [hlam, ← hj']; linarith
      have hlam' : (2 : ℝ) ^ m * t - j = lam / 2 := by rw [hlam, hpow]; push_cast; ring
      rw [hlam', hdisp] at *
      have hd := hdisp j
      have key : x (dyadic m j) + lam * (x (dyadic (m + 1) (2 * j + 1)) - x (dyadic m j)) -
          (x (dyadic m j) + lam / 2 * (x (dyadic m (j + 1)) - x (dyadic m j)))
          = lam * disp x (m + 1) j := by rw [hd]; ring
      rw [key, abs_mul, abs_of_nonneg hl0]
      calc lam * |disp x (m + 1) j| ≤ 1 * |disp x (m + 1) j| :=
            mul_le_mul_of_nonneg_right hl1 (abs_nonneg _)
        _ ≤ maxDisp x (m + 1) := by rw [one_mul]; exact hdle
    · have hjj : j = j' := by rw [hj, hj']; omega
      rw [← hjj] at hj'
      rw [hj', dy2]
      set lam : ℝ := 2 ^ (m + 1) * t - ((2 * j + 1 : ℕ) : ℝ) with hlam
      have hl0 : 0 ≤ lam := by rw [hlam, ← hj']; linarith
      have hl1 : lam ≤ 1 := by rw [hlam, ← hj']; linarith
      have hlam' : (2 : ℝ) ^ m * t - j = (lam + 1) / 2 := by rw [hlam, hpow]; push_cast; ring
      rw [hlam']
      have hd := hdisp j
      have key : x (dyadic (m + 1) (2 * j + 1)) + lam * (x (dyadic m (j + 1)) -
          x (dyadic (m + 1) (2 * j + 1))) -
          (x (dyadic m j) + (lam + 1) / 2 * (x (dyadic m (j + 1)) - x (dyadic m j)))
          = (1 - lam) * disp x (m + 1) j := by rw [hd]; ring
      rw [key, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - lam)]
      calc (1 - lam) * |disp x (m + 1) j| ≤ 1 * |disp x (m + 1) j| :=
            mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
        _ ≤ maxDisp x (m + 1) := by rw [one_mul]; exact hdle
