-- Prove2me | solution 1 for Freiman.rational_adjacent_radius
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T19:57:56.558495+00:00
-- url     : https://prove2.me/submissions/af6f5460-8e90-4f07-b939-a6dde970c643

import Definitions.Def_Freiman_rationalCylinderNeighbors
import Theorems.Thm_Freiman_continuant_append
import Theorems.Thm_Freiman_continuant_denominator_pos
import Theorems.Thm_Freiman_continuant_determinant
import Theorems.Thm_Freiman_prefixEval_mobius
import Theorems.Thm_Freiman_prefixEval_zero
import Mathlib.Tactic.FieldSimp

open Freiman

set_option autoImplicit false

private theorem prev_den_bounds (w : List ℕ+) (hw : w ≠ [])
    (hlast : 2 ≤ ((w.getLastD 1 : ℕ+) : ℕ)) :
    0 < wordContinuantPrevQ w ∧ wordContinuantPrevQ w < wordContinuantQ w := by
  induction w using List.reverseRecOn with
  | nil => exact (hw rfl).elim
  | append_singleton w a ih =>
    have ha : 2 ≤ (a : ℕ) := by simpa using hlast
    have hq := continuant_denominator_pos w
    simp only [wordContinuantPrevQ, wordContinuantQ, continuant_append]
    change 0 < wordContinuantQ w ∧
      wordContinuantQ w < (a : ℕ) * wordContinuantQ w + wordContinuantPrevQ w
    exact ⟨hq, by nlinarith⟩

private theorem adjacent_algebra (p pp q v x : ℝ)
    (hq : 0 < q) (hv : 0 < v) (hvq : v < q)
    (hdet : |pp * q - p * v| = 1)
    (hx : |x - p / q| < 1 / (2 * q ^ 2)) :
    x ∈ Set.Ioo (min ((p + pp) / (q + v)) ((2 * p - pp) / (2 * q - v)))
      (max ((p + pp) / (q + v)) ((2 * p - pp) / (2 * q - v))) := by
  have hqv : 0 < q + v := by linarith
  have h2qv : 0 < 2 * q - v := by linarith
  have hdl : 0 < q * (q + v) := mul_pos hq hqv
  have hdr : 0 < q * (2 * q - v) := mul_pos hq h2qv
  have hbig : 0 < 2 * q ^ 2 := by positivity
  have hl : (p + pp) / (q + v) - p / q = (pp * q - p * v) / (q * (q + v)) := by
    field_simp
    <;> ring
  have hr : (2 * p - pp) / (2 * q - v) - p / q =
      -(pp * q - p * v) / (q * (2 * q - v)) := by
    field_simp
    <;> ring
  have hbl : 1 / (2 * q ^ 2) < 1 / (q * (q + v)) := by
    apply (div_lt_div_iff₀ hbig hdl).mpr
    nlinarith
  have hbr : 1 / (2 * q ^ 2) < 1 / (q * (2 * q - v)) := by
    apply (div_lt_div_iff₀ hbig hdr).mpr
    nlinarith
  have hd : pp * q - p * v = 1 ∨ pp * q - p * v = -1 := by
    rcases le_total 0 (pp * q - p * v) with h | h
    · left
      rwa [abs_of_nonneg h] at hdet
    · right
      rw [abs_of_nonpos h] at hdet
      linarith
  rcases abs_lt.mp hx with ⟨hxlo, hxhi⟩
  rcases hd with hd | hd
  · rw [hd] at hl hr
    simp only [neg_div] at hr
    exact ⟨(min_le_right _ _).trans_lt (by linarith),
      (show x < (p + pp) / (q + v) by linarith).trans_le (le_max_left _ _)⟩
  · rw [hd] at hl hr
    simp only [neg_div, neg_neg] at hl hr
    exact ⟨(min_le_left _ _).trans_lt (by linarith),
      (show x < (2 * p - pp) / (2 * q - v) by linarith).trans_le (le_max_right _ _)⟩

theorem solution (w : List ℕ+) (hw : w ≠ [])
    (hlast : 2 ≤ ((w.getLastD 1 : ℕ+) : ℕ)) (x : ℝ)
    (hx : |x - finiteCF w| < 1 / (2 * (wordContinuantQ w : ℝ) ^ 2)) :
    x ∈ Set.Ioo (min (rationalCylinderNeighborLeft w) (rationalCylinderNeighborRight w))
      (max (rationalCylinderNeighborLeft w) (rationalCylinderNeighborRight w)) := by
  have hpair := prev_den_bounds w hw hlast
  have hq : (0 : ℝ) < wordContinuantQ w := by exact_mod_cast continuant_denominator_pos w
  have hv : (0 : ℝ) < wordContinuantPrevQ w := by exact_mod_cast hpair.1
  have hvq : (wordContinuantPrevQ w : ℝ) < wordContinuantQ w := by exact_mod_cast hpair.2
  have hc : finiteCF w = (wordContinuantP w : ℝ) / wordContinuantQ w := by
    rw [← prefixEval_zero]
    simpa using prefixEval_mobius w 0 (le_refl 0)
  have hdet : |(wordContinuantPrevP w : ℝ) * wordContinuantQ w -
      (wordContinuantP w : ℝ) * wordContinuantPrevQ w| = 1 := by
    have hr : (wordContinuantPrevP w : ℝ) * wordContinuantQ w -
        (wordContinuantP w : ℝ) * wordContinuantPrevQ w = (-1 : ℝ) ^ w.length := by
      exact_mod_cast continuant_determinant w
    rw [hr, abs_pow]
    norm_num
  rw [hc] at hx
  exact adjacent_algebra _ _ _ _ _ hq hv hvq hdet hx
