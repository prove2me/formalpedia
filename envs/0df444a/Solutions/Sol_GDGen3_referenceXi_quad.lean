-- Prove2me | solution 1 for GDGen3.referenceXi_quad
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:33:49.618293+00:00
-- url     : https://prove2.me/submissions/51098301-5494-42bb-9f66-468142f19416

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase

noncomputable section

open Finset

open GDGen3

namespace GDGen3Proof_referenceXi_quad

lemma pj_pos (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (j : ℕ) (hj : j ≠ 0) :
    0 < pj r j := by
  have ht : r ^ (2 * j) < 1 := pow_lt_one₀ (le_of_lt hr) hr1 (by omega)
  exact div_pos (by linarith) (by positivity)

lemma pj_step (r : ℝ) (hr : r ≠ 0) (i : ℕ) :
    r ^ 2 * pj r (i + 1) - pj r i = (1 - r ^ 2) / 2 := by
  simp only [pj, Nat.mul_add, pow_add]
  field_simp
  ring

lemma PiS_closed (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (i : ℕ) :
    PiS r i = pj r i / (1 - r ^ 2) - (i : ℝ) / 2 := by
  have hr2 : r ^ 2 < 1 := pow_lt_one₀ (le_of_lt hr) hr1 (by omega)
  have hne : 1 - r ^ 2 ≠ 0 := by linarith
  induction i with
  | zero => simp [PiS, pj]
  | succ i ih =>
    have hp := pj_step r (ne_of_gt hr) i
    change PiS r (i + 1) = _
    rw [PiS, sum_range_succ]
    change PiS r i + pj r (i + 1) = _
    rw [ih]
    push_cast
    field_simp [hne]
    nlinarith [hp]

lemma rootPoly_expanded (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (v x : ℝ) (i : ℕ) :
    rootPoly r v i x = pj r (i + 1) * x * (1 + x - (1 - r) / (1 + r))
      + v * (i + 1) * x / (1 + r) - v * (i : ℝ) * (i + 1) / (2 * (1 + r))
      + (1 - r) * PiS r i / (1 + r) := by
  have hp : pj r (i + 1) ≠ 0 := ne_of_gt (pj_pos r hr hr1 (i + 1) (by omega))
  unfold rootPoly
  field_simp [hp]
  ring

end GDGen3Proof_referenceXi_quad

open GDGen3Proof_referenceXi_quad

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (i : ℕ) :
    rootPoly r (1 + r) i (referenceXi r i) = 0 := by
  have hr2 : 1 - r ^ 2 ≠ 0 := by
    have ht : r ^ 2 < 1 := pow_lt_one₀ (le_of_lt hr) hr1 (by omega)
    linarith
  have hp : pj r (i + 1) ≠ 0 := ne_of_gt (pj_pos r hr hr1 (i + 1) (by omega))
  rw [rootPoly_expanded r hr hr1]
  unfold referenceXi
  rw [PiS_closed r hr hr1 i]
  unfold pj
  have he : r ^ (2 * i) = (r ^ i) ^ 2 := by rw [Nat.mul_comm 2 i, pow_mul]
  have he1 : r ^ (2 * (i + 1)) = (r ^ i * r) ^ 2 := by
    rw [Nat.mul_comm 2 (i + 1), pow_mul, pow_succ r i]
  rw [he, he1, pow_succ r i]
  set b := r ^ i
  have hbpos : 0 < b := pow_pos hr i
  have hbp : 1 - (b * r) ^ 2 ≠ 0 := by
    have ht : r ^ (2 * (i + 1)) < 1 := pow_lt_one₀ (le_of_lt hr) hr1 (by omega)
    rw [he1] at ht
    change (b * r) ^ 2 < 1 at ht
    linarith
  field_simp [hbp]
  ring
