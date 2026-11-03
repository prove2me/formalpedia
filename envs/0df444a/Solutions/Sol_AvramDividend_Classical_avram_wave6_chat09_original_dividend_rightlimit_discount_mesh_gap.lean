-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_chat09_original_dividend_rightlimit_discount_mesh_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T06:53:24.355042+00:00
-- url     : https://prove2.me/submissions/dfeb9dde-ff77-45b5-9559-fd34e8bb172d

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (u : ℕ → ℝ≥0) (hu : Monotone u)
    (n : ℕ) (m : ℝ) (hm : 0 ≤ m)
    (hmesh : ∀ i < n, ((u (i + 1) : ℝ) - (u i : ℝ)) ≤ m) :
    (∑ i ∈ Finset.range n,
      (Real.exp (-(q * (u i : ℝ))) -
         Real.exp (-(q * (u (i + 1) : ℝ)))) *
       (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω)) ≤
       q * m * (rightLimit D (u n) ω - rightLimit D (u 0) ω) := by
  have hDmon : Monotone (fun t : ℝ≥0 => rightLimit D t ω) :=
    avram_wave3_03_dividendStrategy_rightLimit_monotone D hD ω
  have hExpGap (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
      Real.exp (-(q * a)) - Real.exp (-(q * b)) ≤ q * (b - a) := by
    have hqdelta : 0 ≤ q * (b - a) := mul_nonneg hq (sub_nonneg.mpr hab)
    have hepos : 0 ≤ Real.exp (-(q * a)) := le_of_lt (Real.exp_pos _)
    have hele : Real.exp (-(q * a)) ≤ 1 :=
      (Real.exp_le_one_iff).2 (neg_nonpos.mpr (mul_nonneg hq ha))
    have htangent := Real.add_one_le_exp (-(q * (b - a)))
    have hsmall : 1 - Real.exp (-(q * (b - a))) ≤ q * (b - a) := by
      linarith
    have heq : Real.exp (-(q * b)) =
        Real.exp (-(q * a)) * Real.exp (-(q * (b - a))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq]
    calc
      Real.exp (-(q * a)) -
          Real.exp (-(q * a)) * Real.exp (-(q * (b - a))) =
        Real.exp (-(q * a)) * (1 - Real.exp (-(q * (b - a)))) := by ring
      _ ≤ Real.exp (-(q * a)) * (q * (b - a)) :=
        mul_le_mul_of_nonneg_left hsmall hepos
      _ ≤ 1 * (q * (b - a)) :=
        mul_le_mul_of_nonneg_right hele hqdelta
      _ = q * (b - a) := one_mul _
  have hCell (i : ℕ) (hi : i ∈ Finset.range n) :
      (Real.exp (-(q * (u i : ℝ))) -
          Real.exp (-(q * (u (i + 1) : ℝ)))) *
          (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω) ≤
        (q * m) *
          (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω) := by
    have hui : u i ≤ u (i + 1) := hu (Nat.le_succ i)
    have ha : 0 ≤ (u i : ℝ) := NNReal.coe_nonneg _
    have hab : (u i : ℝ) ≤ (u (i + 1) : ℝ) := by exact_mod_cast hui
    have hdiff : 0 ≤
        rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω :=
      sub_nonneg.mpr (hDmon hui)
    have hgap : Real.exp (-(q * (u i : ℝ))) -
        Real.exp (-(q * (u (i + 1) : ℝ))) ≤ q * m :=
      (hExpGap _ _ ha hab).trans
        (mul_le_mul_of_nonneg_left (hmesh i (Finset.mem_range.mp hi)) hq)
    exact mul_le_mul_of_nonneg_right hgap hdiff
  have hTel (k : ℕ) :
      (∑ i ∈ Finset.range k,
        (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω)) =
      rightLimit D (u k) ω - rightLimit D (u 0) ω := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  calc
    (∑ i ∈ Finset.range n,
      (Real.exp (-(q * (u i : ℝ))) -
         Real.exp (-(q * (u (i + 1) : ℝ)))) *
       (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω)) ≤
      ∑ i ∈ Finset.range n,
        (q * m) *
          (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω) :=
        Finset.sum_le_sum hCell
    _ = q * m * (rightLimit D (u n) ω - rightLimit D (u 0) ω) := by
      rw [← Finset.mul_sum, hTel n]
