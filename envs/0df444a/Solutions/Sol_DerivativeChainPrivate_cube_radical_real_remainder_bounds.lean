-- Prove2me | solution 1 for DerivativeChainPrivate.cube_radical_real_remainder_bounds
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T04:08:40.180992+00:00
-- url     : https://prove2.me/submissions/ad8cbf84-0ffc-4807-b125-50551990f587

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem solution (x y p D a b r : ℝ)
    (hx : 0 < x) (hy : y ≠ 0) (hU : 5 / 2 ≤ x ^ 2 + y ^ 2)
    (hp : 9 / 10 ≤ p) (hD : 3 ≤ D)
    (ha : 2 / 5 ≤ a) (ha' : a ≤ 3 / 5) (hab : a ^ 2 + b ^ 2 ≤ (3 / 5 : ℝ) ^ 2)
    (hr : 0 ≤ r) (hr' : r ≤ 3 / 2)
    (hkey : 6 * p * (x ^ 2 + y ^ 2) ^ 2 * D * b = x * y) :
    let U := x ^ 2 + y ^ 2
    let P := 16 * a + a ^ 2 - b ^ 2
    let Q := b * (16 + 2 * a)
    let A := r / (336 * U) * (P + (y / x) * Q)
    let B := r / (336 * U) * ((x / y) * Q - P)
    0 ≤ A ∧ A ≤ 1 / 50 ∧ -(1 / 50) ≤ B ∧ B ≤ 0 ∧
      0 ≤ (3 * A - B) / 2 ∧ (3 * A - B) / 2 ≤ 1 / 25 := by
  let U := x ^ 2 + y ^ 2
  have hUpos : 0 < U := by dsimp only [U]; linarith
  have hpD : 27 / 10 ≤ p * D := by
    have hmul := mul_nonneg (show 0 ≤ p - 9 / 10 by linarith) (show 0 ≤ D - 3 by linarith)
    nlinarith only [hmul, hp, hD]
  have hden : 40 * U ≤ 6 * p * U ^ 2 * D := by
    have hmul := mul_le_mul_of_nonneg_right hpD hUpos.le
    have hK : 40 ≤ 6 * p * U * D := by nlinarith only [hmul, hU]
    have hmul' := mul_le_mul_of_nonneg_right hK hUpos.le
    nlinarith only [hmul']
  have hdenpos : 0 < 6 * p * U ^ 2 * D := by nlinarith only [hden,hUpos]
  have hq₀ : (y / x) * b = y ^ 2 / (6 * p * U ^ 2 * D) := by
    apply (eq_div_iff hdenpos.ne').2
    calc
      _ = (y / x) * (6 * p * U ^ 2 * D * b) := by ring
      _ = (y / x) * (x * y) := by rw [hkey]
      _ = y ^ 2 := by field_simp
  have hq₁ : (x / y) * b = x ^ 2 / (6 * p * U ^ 2 * D) := by
    apply (eq_div_iff hdenpos.ne').2
    calc
      _ = (x / y) * (6 * p * U ^ 2 * D * b) := by ring
      _ = (x / y) * (x * y) := by rw [hkey]
      _ = x ^ 2 := by field_simp
  have hrat₀ : 0 ≤ (y / x) * b ∧ (y / x) * b ≤ 1 / 40 := by
    rw [hq₀]
    constructor
    · positivity
    · apply (div_le_iff₀ hdenpos).2
      dsimp only [U] at hden
      nlinarith only [hden, sq_nonneg x]
  have hrat₁ : 0 ≤ (x / y) * b ∧ (x / y) * b ≤ 1 / 40 := by
    rw [hq₁]
    constructor
    · positivity
    · apply (div_le_iff₀ hdenpos).2
      dsimp only [U] at hden
      nlinarith only [hden, sq_nonneg y]
  have hQ₀ : 0 ≤ (y / x) * (b * (16 + 2 * a)) ∧
      (y / x) * (b * (16 + 2 * a)) ≤ 1 / 2 := by
    rw [← mul_assoc]
    constructor
    · exact mul_nonneg hrat₀.1 (by linarith)
    · have h := mul_le_mul hrat₀.2 (show 16 + 2 * a ≤ 86 / 5 by linarith)
        (by linarith : 0 ≤ 16 + 2 * a) (by norm_num : (0 : ℝ) ≤ 1 / 40)
      linarith
  have hQ₁ : 0 ≤ (x / y) * (b * (16 + 2 * a)) ∧
      (x / y) * (b * (16 + 2 * a)) ≤ 1 / 2 := by
    rw [← mul_assoc]
    constructor
    · exact mul_nonneg hrat₁.1 (by linarith)
    · have h := mul_le_mul hrat₁.2 (show 16 + 2 * a ≤ 86 / 5 by linarith)
        (by linarith : 0 ≤ 16 + 2 * a) (by norm_num : (0 : ℝ) ≤ 1 / 40)
      linarith
  have hP : 6 ≤ 16 * a + a ^ 2 - b ^ 2 ∧ 16 * a + a ^ 2 - b ^ 2 ≤ 10 := by
    constructor <;> nlinarith only [ha,ha',hab,sq_nonneg a,sq_nonneg b]
  have hfac : 0 ≤ r / (336 * U) ∧ r / (336 * U) ≤ 1 / 560 := by
    constructor
    · positivity
    · apply (div_le_iff₀ (by positivity : 0 < 336 * U)).2
      dsimp only [U]
      linarith
  dsimp only
  change 0 ≤ r / (336 * U) * _ ∧ _
  have hA₀ : 0 ≤ r / (336 * U) * (16 * a + a ^ 2 - b ^ 2 + (y / x) * (b * (16 + 2 * a))) :=
    mul_nonneg hfac.1 (by linarith only [hP.1,hQ₀.1])
  have hA₁ : r / (336 * U) * (16 * a + a ^ 2 - b ^ 2 + (y / x) * (b * (16 + 2 * a))) ≤ 1 / 50 := by
    have h := mul_le_mul hfac.2 (show 16 * a + a ^ 2 - b ^ 2 +
      (y / x) * (b * (16 + 2 * a)) ≤ 21 / 2 by linarith only [hP.2,hQ₀.2])
      (by linarith only [hP.1,hQ₀.1] : 0 ≤ 16 * a + a ^ 2 - b ^ 2 + (y / x) * (b * (16 + 2 * a)))
      (by norm_num : (0 : ℝ) ≤ 1 / 560)
    linarith
  have hB₀ : -(1 / 50 : ℝ) ≤ r / (336 * U) * ((x / y) * (b * (16 + 2 * a)) -
      (16 * a + a ^ 2 - b ^ 2)) := by
    have h := mul_nonneg hfac.1 (show 0 ≤ (x / y) * (b * (16 + 2 * a)) -
      (16 * a + a ^ 2 - b ^ 2) + 10 by linarith only [hP.2,hQ₁.1])
    nlinarith only [h,hfac.2]
  have hB₁ : r / (336 * U) * ((x / y) * (b * (16 + 2 * a)) - (16 * a + a ^ 2 - b ^ 2)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hfac.1 (by linarith only [hQ₁.2,hP.1])
  exact ⟨hA₀,hA₁,hB₀,hB₁,by linarith only [hA₀,hB₁],by linarith only [hA₁,hB₀]⟩
