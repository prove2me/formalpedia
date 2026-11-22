-- Prove2me | solution 1 for DPVerify.clip_mass_le
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-22T12:43:48.706966+00:00
-- url     : https://prove2.me/submissions/e472e715-47be-4af0-8607-88befa614ae3

import Mathlib

set_option autoImplicit false

theorem solution {M : Type} [Fintype M] (p p' : M → ℝ) (hp : ∀ m, 0 ≤ p m)
    (hp' : ∀ m, 0 ≤ p' m) (ε δ : ℝ) (hε : 0 ≤ ε)
    (h1 : ∀ E : Finset M, ∑ m ∈ E, p m ≤ Real.exp ε * ∑ m ∈ E, p' m + δ)
    (h2 : ∀ E : Finset M, ∑ m ∈ E, p' m ≤ Real.exp ε * ∑ m ∈ E, p m + δ) :
    ∑ m, |p m - min (Real.exp ε * p' m) (max (Real.exp (-ε) * p' m) (p m))| ≤ 2 * δ := by
  classical
  have hδ : 0 ≤ δ := by
    have h := h1 (∅ : Finset M)
    simpa using h
  -- pointwise identity
  have hpoint : ∀ m, |p m - min (Real.exp ε * p' m) (max (Real.exp (-ε) * p' m) (p m))|
      = max (p m - Real.exp ε * p' m) 0 + max (Real.exp (-ε) * p' m - p m) 0 := by
    intro m
    have hxn : 0 ≤ p m := hp m
    have hyn : 0 ≤ p' m := hp' m
    have hlo : 0 ≤ Real.exp (-ε) * p' m := by positivity
    have hhi : 0 ≤ Real.exp ε * p' m := by positivity
    have hleh : Real.exp (-ε) ≤ Real.exp ε := Real.exp_le_exp.mpr (by linarith)
    have hlohi : Real.exp (-ε) * p' m ≤ Real.exp ε * p' m :=
      mul_le_mul_of_nonneg_right hleh (hp' m)
    rcases lt_or_ge (p m) (Real.exp (-ε) * p' m) with hlt | hge
    · -- p < e^{-ε} p'
      have hmax : max (Real.exp (-ε) * p' m) (p m) = Real.exp (-ε) * p' m := max_eq_left hlt.le
      have hmin : min (Real.exp ε * p' m) (Real.exp (-ε) * p' m) = Real.exp (-ε) * p' m :=
        min_eq_right hlohi
      rw [hmax, hmin, abs_of_nonpos (by linarith : p m - Real.exp (-ε) * p' m ≤ 0)]
      rw [max_eq_right (by linarith : p m - Real.exp ε * p' m ≤ 0),
        max_eq_left (by linarith : (0 : ℝ) ≤ Real.exp (-ε) * p' m - p m)]
      ring
    · rcases le_or_gt (p m) (Real.exp ε * p' m) with hle | hgt
      · -- e^{-ε} p' ≤ p ≤ e^ε p'
        have hmax : max (Real.exp (-ε) * p' m) (p m) = p m := max_eq_right hge
        have hmin : min (Real.exp ε * p' m) (p m) = p m := min_eq_right hle
        rw [hmax, hmin, sub_self, abs_zero]
        rw [max_eq_right (by linarith : p m - Real.exp ε * p' m ≤ 0),
          max_eq_right (by linarith : Real.exp (-ε) * p' m - p m ≤ 0)]
        ring
      · -- p > e^ε p'
        have hmax : max (Real.exp (-ε) * p' m) (p m) = p m := max_eq_right hge
        have hmin : min (Real.exp ε * p' m) (p m) = Real.exp ε * p' m := min_eq_left hgt.le
        rw [hmax, hmin, abs_of_nonneg (by linarith : (0 : ℝ) ≤ p m - Real.exp ε * p' m)]
        rw [max_eq_left (by linarith : (0 : ℝ) ≤ p m - Real.exp ε * p' m),
          max_eq_right (by linarith : Real.exp (-ε) * p' m - p m ≤ 0)]
        ring
  -- the two regions
  set A : Finset M := Finset.univ.filter (fun m => Real.exp ε * p' m < p m) with hA
  set B : Finset M := Finset.univ.filter (fun m => p m < Real.exp (-ε) * p' m) with hB
  have hA_eq : ∑ m, max (p m - Real.exp ε * p' m) 0
      = ∑ m ∈ A, (p m - Real.exp ε * p' m) := by
    rw [hA, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro m _
    by_cases h : Real.exp ε * p' m < p m
    · rw [max_eq_left (by linarith : (0 : ℝ) ≤ p m - Real.exp ε * p' m), if_pos h]
    · rw [max_eq_right (by linarith : p m - Real.exp ε * p' m ≤ 0), if_neg h]
  have hB_eq : ∑ m, max (Real.exp (-ε) * p' m - p m) 0
      = ∑ m ∈ B, (Real.exp (-ε) * p' m - p m) := by
    rw [hB, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro m _
    by_cases h : p m < Real.exp (-ε) * p' m
    · rw [max_eq_left (by linarith : (0 : ℝ) ≤ Real.exp (-ε) * p' m - p m), if_pos h]
    · rw [max_eq_right (by linarith : Real.exp (-ε) * p' m - p m ≤ 0), if_neg h]
  -- bound on A from h1
  have hA_bound : ∑ m ∈ A, (p m - Real.exp ε * p' m) ≤ δ := by
    have h := h1 A
    have hsum : ∑ m ∈ A, (p m - Real.exp ε * p' m)
        = ∑ m ∈ A, p m - Real.exp ε * ∑ m ∈ A, p' m := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hsum]
    linarith
  -- bound on B from h2
  have hB_bound : ∑ m ∈ B, (Real.exp (-ε) * p' m - p m) ≤ δ := by
    have h := h2 B
    have hexpneg_le_one : Real.exp (-ε) ≤ 1 := by
      simpa using Real.exp_le_exp.mpr (by linarith : -ε ≤ 0)
    have hsum : ∑ m ∈ B, (Real.exp (-ε) * p' m - p m)
        = Real.exp (-ε) * ∑ m ∈ B, p' m - ∑ m ∈ B, p m := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hsum]
    have hmul : Real.exp (-ε) * ∑ m ∈ B, p' m
        ≤ Real.exp (-ε) * (Real.exp ε * ∑ m ∈ B, p m + δ) :=
      mul_le_mul_of_nonneg_left h (Real.exp_pos (-ε)).le
    have hcancel : Real.exp (-ε) * Real.exp ε = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have h2' : Real.exp (-ε) * δ ≤ δ := by
      calc Real.exp (-ε) * δ ≤ 1 * δ := mul_le_mul_of_nonneg_right hexpneg_le_one hδ
        _ = δ := by ring
    have hmul' : Real.exp (-ε) * ∑ m ∈ B, p' m ≤ ∑ m ∈ B, p m + Real.exp (-ε) * δ := by
      calc Real.exp (-ε) * ∑ m ∈ B, p' m
          ≤ Real.exp (-ε) * (Real.exp ε * ∑ m ∈ B, p m + δ) := hmul
        _ = ∑ m ∈ B, p m + Real.exp (-ε) * δ := by
            rw [mul_add, ← mul_assoc, hcancel, one_mul]
    linarith
  -- assemble
  calc ∑ m, |p m - min (Real.exp ε * p' m) (max (Real.exp (-ε) * p' m) (p m))|
      = ∑ m, (max (p m - Real.exp ε * p' m) 0
          + max (Real.exp (-ε) * p' m - p m) 0) := by
          apply Finset.sum_congr rfl
          intro m _
          exact hpoint m
    _ = ∑ m, max (p m - Real.exp ε * p' m) 0
          + ∑ m, max (Real.exp (-ε) * p' m - p m) 0 := Finset.sum_add_distrib
    _ = ∑ m ∈ A, (p m - Real.exp ε * p' m)
          + ∑ m ∈ B, (Real.exp (-ε) * p' m - p m) := by rw [hA_eq, hB_eq]
    _ ≤ δ + δ := add_le_add hA_bound hB_bound
    _ = 2 * δ := by ring

