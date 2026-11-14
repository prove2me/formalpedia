-- Prove2me | solution 1 for ConsistentSubmodular.LowRollback.eligible_low_credit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:26:39.426194+00:00
-- url     : https://prove2.me/submissions/3d6d796f-99c0-4430-84df-0b1b5d44a0f0

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_LowRollbackTargets

section

namespace ConsistentSubmodular.LowRollback

theorem eligible_low_polynomials (k : ℝ) (hk0 : 40 / 23 ≤ k) (hk1 : k ≤ 20 / 11) :
    0 < -5 * k ^ 2 + 54 * k - 72 ∧
    0 < (319 * k ^ 3 + 6081 * k ^ 2 - 27843 * k + 28800) / 1600 ∧
    0 < (4805 * k ^ 2 - 11574 * k + 5832) / 1600 := by
  let x := (k - 40 / 23) / (20 / 11 - 40 / 23)
  have hx0 : 0 ≤ x := by
    dsimp [x]
    exact div_nonneg (sub_nonneg.mpr hk0) (by norm_num)
  have hx1 : x ≤ 1 := by dsimp [x]; apply (div_le_one (by norm_num)).mpr; linarith
  have hy : 0 ≤ 1 - x := by linarith
  have hk : k = 40 / 23 + (20 / 11 - 40 / 23) * x := by dsimp [x]; ring
  have hA : -5 * k ^ 2 + 54 * k - 72 = 6+
      (3592 / 529 - 6) * (1 - x) ^ 2 + 2 * (2084 / 253 - 6) * x * (1 - x) + (1168 / 121 - 6) * x ^ 2 := by
    rw [hk]; ring
  have hN0 : (319 * k ^ 3 + 6081 * k ^ 2 - 27843 * k + 28800) / 1600 = 1 / 10+
      (136213 / 486680 - 1 / 10) * (1 - x) ^ 3 + 3 * (101179 / 465520 - 1 / 10) * x * (1 - x) ^ 2+
      3 * (4589 / 27830 - 1 / 10) * x ^ 2 * (1 - x) + (1187 / 9680 - 1 / 10) * x ^ 3 := by
    rw [hk]; ring
  have hN1 : (4805 * k ^ 2 - 11574 * k + 5832) / 1600 = 1 / 10+
      (15631 / 105800 - 1 / 10) * (1 - x) ^ 2 + 2 * (27799 / 101200 - 1 / 10) * x * (1 - x)+
      (5087 / 12100 - 1 / 10) * x ^ 2 := by
    rw [hk]; ring
  rw [hA, hN0, hN1]
  norm_num
  constructor
  · positivity
  constructor <;> positivity

end ConsistentSubmodular.LowRollback

end

section

open ConsistentSubmodular ConsistentSubmodular.LowRollback

theorem solution (k d₀ d p W : ℝ)
    (hk0 : 40 / 23 ≤ k) (hk1 : k ≤ 20 / 11)
    (hd : 319 / 1600 ≤ d) (hd₀ : 0 ≤ d₀) (hd₀d : d₀ ≤ d)
    (hatt : p = (4 - k) * W - k * d - (4 - k) * d₀) (hweak : W + d₀ ≤ p) :
    0 < U k d₀ d p W := by
  let A := k * (k ^ 2 - k + 3)
  let B := -k ^ 3 - 4 * k ^ 2 + 51 * k - 72
  let C₀ := (4 * k - 6) * (k - 3)
  have hk : 0 < k := by linarith
  have hden : 0 < k * (3 - k) := by apply mul_pos hk; linarith
  have hcoef : 0 ≤ k * (9 - 2 * k) := by apply mul_nonneg hk.le; linarith
  have hA : 0 < A := by
    dsimp [A]
    apply mul_pos hk
    nlinarith [sq_nonneg (k - 1 / 2)]
  obtain ⟨hAB, hN0, hN1⟩ := eligible_low_polynomials k hk0 hk1
  have hiden : k * (3 - k) * U k d₀ d p W =
      k * (9 - 2 * k) * (p - W - d₀) + d * A + d₀ * B + C₀ := by
    rw [hatt]
    unfold U ceiling
    dsimp [A, B, C₀]
    field_simp
    ring
  have hJ := mul_nonneg hcoef (show 0 ≤ p - W - d₀ by linarith)
  have hrest : 0 < d * A + d₀ * B + C₀ := by
    by_cases hB : 0 ≤ B
    · have hb := mul_nonneg hd₀ hB
      have ha := mul_nonneg (show 0 ≤ d - 319 / 1600 by linarith) hA.le
      have heq : (319 / 1600) * A + C₀ = (319 * k ^ 3 + 6081 * k ^ 2 - 27843 * k + 28800) / 1600 := by
        dsimp [A, C₀]; ring
      linarith
    · have hB' : B ≤ 0 := le_of_not_ge hB
      have hb := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hd₀d) hB'
      have heqAB : A + B = -5 * k ^ 2 + 54 * k - 72 := by dsimp [A, B]; ring
      have ha := mul_nonneg (show 0 ≤ d - 319 / 1600 by linarith) (le_of_lt hAB)
      have heq : (319 / 1600) * (A + B) + C₀ = (4805 * k ^ 2 - 11574 * k + 5832) / 1600 := by
        dsimp [A, B, C₀]; ring
      rw [← heqAB] at ha
      nlinarith
  have hu : 0 < k * (3 - k) * U k d₀ d p W := by rw [hiden]; linarith
  exact (mul_pos_iff_of_pos_left hden).mp hu

end
