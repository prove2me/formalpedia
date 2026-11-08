-- Prove2me | solution 1 for FuchsVdGraaf.proposition_5_43
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:50:29.285128+00:00
-- url     : https://prove2.me/submissions/98fa58ae-cf6d-4cdf-8135-6ce13b904e0b

import Mathlib
import Definitions.Def_FuchsVdGraaf_IsProbDist
import Definitions.Def_FuchsVdGraaf_kolmogorov
import Definitions.Def_FuchsVdGraaf_bhattacharyya

open FuchsVdGraaf in
theorem solution {X : Type} [Fintype X] (p0 p1 : X → ℝ)
    (hp0 : FuchsVdGraaf.IsProbDist p0) (hp1 : FuchsVdGraaf.IsProbDist p1) :
    1 - FuchsVdGraaf.bhattacharyya p0 p1 ≤ FuchsVdGraaf.kolmogorov p0 p1 ∧
      FuchsVdGraaf.kolmogorov p0 p1 ≤ Real.sqrt (1 - FuchsVdGraaf.bhattacharyya p0 p1 ^ 2) := by
  obtain ⟨h0n, h0s⟩ := hp0
  obtain ⟨h1n, h1s⟩ := hp1
  have hs2 : ∀ x, Real.sqrt (p0 x) ^ 2 = p0 x := fun x => Real.sq_sqrt (h0n x)
  have ht2 : ∀ x, Real.sqrt (p1 x) ^ 2 = p1 x := fun x => Real.sq_sqrt (h1n x)
  have hst : ∀ x, Real.sqrt (p0 x * p1 x) = Real.sqrt (p0 x) * Real.sqrt (p1 x) :=
    fun x => Real.sqrt_mul (h0n x) _
  have habs : ∀ x, |p0 x - p1 x| =
      |Real.sqrt (p0 x) - Real.sqrt (p1 x)| * (Real.sqrt (p0 x) + Real.sqrt (p1 x)) := by
    intro x
    rw [← abs_of_nonneg (add_nonneg (Real.sqrt_nonneg (p0 x)) (Real.sqrt_nonneg (p1 x))),
      ← abs_mul]
    congr 1
    rw [show (Real.sqrt (p0 x) - Real.sqrt (p1 x)) * (Real.sqrt (p0 x) + Real.sqrt (p1 x)) =
      Real.sqrt (p0 x) ^ 2 - Real.sqrt (p1 x) ^ 2 by ring, hs2, ht2]
  unfold FuchsVdGraaf.bhattacharyya FuchsVdGraaf.kolmogorov
  simp only [hst, habs]
  obtain ⟨B, hB⟩ : ∃ B, B = ∑ x, Real.sqrt (p0 x) * Real.sqrt (p1 x) := ⟨_, rfl⟩
  rw [← hB]
  have hdiff : ∑ x, (Real.sqrt (p0 x) - Real.sqrt (p1 x)) ^ 2 = 2 - 2 * B := by
    have e : ∀ x, (Real.sqrt (p0 x) - Real.sqrt (p1 x)) ^ 2 =
        p0 x + p1 x - 2 * (Real.sqrt (p0 x) * Real.sqrt (p1 x)) := by
      intro x; linear_combination (hs2 x) + (ht2 x)
    rw [Finset.sum_congr rfl (fun x _ => e x), Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, h0s, h1s, ← hB]
    ring
  have hsum : ∑ x, (Real.sqrt (p0 x) + Real.sqrt (p1 x)) ^ 2 = 2 + 2 * B := by
    have e : ∀ x, (Real.sqrt (p0 x) + Real.sqrt (p1 x)) ^ 2 =
        p0 x + p1 x + 2 * (Real.sqrt (p0 x) * Real.sqrt (p1 x)) := by
      intro x; linear_combination (hs2 x) + (ht2 x)
    rw [Finset.sum_congr rfl (fun x _ => e x), Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, h0s, h1s, ← hB]
    ring
  have hterm : ∀ x, (Real.sqrt (p0 x) - Real.sqrt (p1 x)) ^ 2 ≤
      |Real.sqrt (p0 x) - Real.sqrt (p1 x)| * (Real.sqrt (p0 x) + Real.sqrt (p1 x)) := by
    intro x
    rw [← sq_abs, sq]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    rw [abs_sub_le_iff]
    constructor <;> linarith [Real.sqrt_nonneg (p0 x), Real.sqrt_nonneg (p1 x)]
  have hK0 : 0 ≤ (1 / 2) * ∑ x, |Real.sqrt (p0 x) - Real.sqrt (p1 x)| *
      (Real.sqrt (p0 x) + Real.sqrt (p1 x)) := by
    apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg (fun x _ => mul_nonneg (abs_nonneg _)
      (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
  constructor
  · have := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hterm x)
    rw [hdiff] at this
    linarith
  · have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun x => |Real.sqrt (p0 x) - Real.sqrt (p1 x)|)
      (fun x => Real.sqrt (p0 x) + Real.sqrt (p1 x))
    simp only [sq_abs] at hcs
    rw [hdiff, hsum] at hcs
    have hK2 : ((1 / 2) * ∑ x, |Real.sqrt (p0 x) - Real.sqrt (p1 x)| *
        (Real.sqrt (p0 x) + Real.sqrt (p1 x))) ^ 2 ≤ 1 - B ^ 2 := by
      nlinarith [hcs]
    rw [← Real.sqrt_sq hK0]
    exact Real.sqrt_le_sqrt hK2
