-- Prove2me | solution 1 for BanditAlgorithm.partial_monitoring_hard_tradeoff_analytic
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T17:03:08.970128+00:00
-- url     : https://prove2.me/submissions/0ec0dfcb-3912-42e7-ac01-f125b1cadb6b

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

#check Real.rpow_add
#check Real.rpow_mul
#check Real.rpow_neg
#check Real.rpow_le_rpow
#check Real.exp_le_exp

open Real

theorem rpow_one_third_mul {n : ℝ} (hn : 0 < n) :
    n * n ^ (-(1 : ℝ) / 3) = n ^ ((2 : ℝ) / 3) := by
  calc
    n * n ^ (-(1 : ℝ) / 3) = n ^ (1 : ℝ) * n ^ (-(1 : ℝ) / 3) := by
      rw [Real.rpow_one]
    _ = n ^ ((1 : ℝ) + (-(1 : ℝ) / 3)) := (Real.rpow_add hn 1 _).symm
    _ = n ^ ((2 : ℝ) / 3) := by congr 1 <;> ring

theorem rpow_cancel_thirds {n δ : ℝ} (hn : 0 < n) :
    (δ * n ^ (-(1 : ℝ) / 3)) ^ 2 * n ^ ((2 : ℝ) / 3) = δ ^ 2 := by
  have hn2 : (n ^ (-(1 : ℝ) / 3)) ^ (2 : ℕ) = n ^ (-(1 : ℝ) / 3 * 2) := by
    rw [← Real.rpow_natCast]
    exact (Real.rpow_mul hn.le _ _).symm
  have hzero : n ^ (-(1 : ℝ) / 3 * 2 + (2 : ℝ) / 3) = 1 := by
    convert Real.rpow_zero n using 2 <;> ring
  calc
    (δ * n ^ (-(1 : ℝ) / 3)) ^ 2 * n ^ ((2 : ℝ) / 3) =
        δ ^ 2 * ((n ^ (-(1 : ℝ) / 3)) ^ 2 * n ^ ((2 : ℝ) / 3)) := by ring
    _ = δ ^ 2 * (n ^ (-(1 : ℝ) / 3 * 2) * n ^ ((2 : ℝ) / 3)) := by rw [hn2]
    _ = δ ^ 2 * n ^ (-(1 : ℝ) / 3 * 2 + (2 : ℝ) / 3) := by
      rw [Real.rpow_add hn]
    _ = δ ^ 2 := by rw [hzero, mul_one]

theorem hard_tradeoff_analytic
    (ε C δ : ℝ) (hε : 0 < ε) (hC : 0 ≤ C) (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ), 1 ≤ n → ∀ x : ℝ, 0 ≤ x →
      ε / 2 * x +
          (n : ℝ) * (δ * (n : ℝ) ^ (-(1 : ℝ) / 3)) / 8 *
            Real.exp (-C * (δ * (n : ℝ) ^ (-(1 : ℝ) / 3)) ^ 2 * x) ≥
        c * (n : ℝ) ^ ((2 : ℝ) / 3) := by
  let c := min (ε / 2) (δ / 8 * Real.exp (-C * δ ^ 2))
  refine ⟨c, ?_, ?_⟩
  · dsimp [c]
    exact lt_min (div_pos hε (by norm_num))
      (mul_pos (div_pos hδ (by norm_num)) (Real.exp_pos _))
  · intro n hn x hx
    have hnR : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
    have hn0 : 0 ≤ (n : ℝ) := hnR.le
    by_cases hlarge : (n : ℝ) ^ ((2 : ℝ) / 3) ≤ x
    · have hfirst : c * (n : ℝ) ^ ((2 : ℝ) / 3) ≤ ε / 2 * x := by
        apply le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.rpow_nonneg hn0 _))
        exact mul_le_mul_of_nonneg_left hlarge (le_of_lt (div_pos hε (by norm_num)))
      have hsecond : 0 ≤
          (n : ℝ) * (δ * (n : ℝ) ^ (-(1 : ℝ) / 3)) / 8 *
            Real.exp (-C * (δ * (n : ℝ) ^ (-(1 : ℝ) / 3)) ^ 2 * x) := by
        exact mul_nonneg
          (div_nonneg
            (mul_nonneg hn0 (mul_nonneg hδ.le (Real.rpow_nonneg hn0 _))) (by norm_num))
          (Real.exp_pos _).le
      linarith

    · have hxlt : x < (n : ℝ) ^ ((2 : ℝ) / 3) := lt_of_not_ge hlarge
      have hpow : (δ * (n : ℝ) ^ (-(1 : ℝ) / 3)) ^ 2 * x ≤ δ ^ 2 := by
        calc
          _ ≤ (δ * (n : ℝ) ^ (-(1 : ℝ) / 3)) ^ 2 *
              (n : ℝ) ^ ((2 : ℝ) / 3) :=
            mul_le_mul_of_nonneg_left hxlt.le (sq_nonneg _)
          _ = δ ^ 2 := rpow_cancel_thirds hnR
      have hexp : Real.exp (-C * δ ^ 2) ≤
          Real.exp (-C * (δ * (n : ℝ) ^ (-(1 : ℝ) / 3)) ^ 2 * x) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      have hnscale : (n : ℝ) * (δ * (n : ℝ) ^ (-(1 : ℝ) / 3)) / 8 =
          δ / 8 * (n : ℝ) ^ ((2 : ℝ) / 3) := by
        calc
          _ = δ / 8 * ((n : ℝ) * (n : ℝ) ^ (-(1 : ℝ) / 3)) := by ring
          _ = _ := by rw [rpow_one_third_mul hnR]
      have hsecond : c * (n : ℝ) ^ ((2 : ℝ) / 3) ≤
          (n : ℝ) * (δ * (n : ℝ) ^ (-(1 : ℝ) / 3)) / 8 *
            Real.exp (-C * (δ * (n : ℝ) ^ (-(1 : ℝ) / 3)) ^ 2 * x) := by
        rw [hnscale]
        calc
          c * (n : ℝ) ^ ((2 : ℝ) / 3) ≤
              (δ / 8 * Real.exp (-C * δ ^ 2)) *
                (n : ℝ) ^ ((2 : ℝ) / 3) :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.rpow_nonneg hn0 _)
          _ ≤ (δ / 8 * (n : ℝ) ^ ((2 : ℝ) / 3)) *
                Real.exp (-C * (δ * (n : ℝ) ^ (-(1 : ℝ) / 3)) ^ 2 * x) := by
            have hcoef : 0 ≤ δ / 8 * (n : ℝ) ^ ((2 : ℝ) / 3) := by positivity
            calc
              _ = (δ / 8 * (n : ℝ) ^ ((2 : ℝ) / 3)) * Real.exp (-C * δ ^ 2) := by ring
              _ ≤ _ := mul_le_mul_of_nonneg_left hexp hcoef
      have hfirst : 0 ≤ ε / 2 * x := mul_nonneg (div_nonneg hε.le (by norm_num)) hx
      linarith

theorem solution
    (ε C δ : ℝ) (hε : 0 < ε) (hC : 0 ≤ C) (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ), 1 ≤ n → ∀ x : ℝ, 0 ≤ x →
      ε / 2 * x +
          (n : ℝ) * (δ * (n : ℝ) ^ (-(1 : ℝ) / 3)) / 8 *
            Real.exp (-C * (δ * (n : ℝ) ^ (-(1 : ℝ) / 3)) ^ 2 * x) ≥
        c * (n : ℝ) ^ ((2 : ℝ) / 3) :=
  hard_tradeoff_analytic ε C δ hε hC hδ
