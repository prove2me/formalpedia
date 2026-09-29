-- Prove2me | solution 1 for Freiman.lowerHistory_cf_from_inverse
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T00:28:16.340006+00:00
-- url     : https://prove2.me/submissions/7bdc55e3-7f2e-4596-92d7-8977f9bb5f2c

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic

open Freiman

-- The certificate field is a Q-algebra model of Q(sqrt 3, sqrt 7) and
-- `certFieldVal` is its evaluation in the reals.
lemma cfw_add (x y : CertField) :
    certFieldVal (certFieldAdd x y) = certFieldVal x + certFieldVal y := by
  simp only [certFieldVal, certFieldAdd]
  push_cast
  ring

lemma cfw_scale (q : ℚ) (x : CertField) :
    certFieldVal (certFieldScale q x) = (q : ℝ) * certFieldVal x := by
  simp only [certFieldVal, certFieldScale]
  push_cast
  ring

lemma cfw_mul (x y : CertField) :
    certFieldVal (certFieldMul x y) = certFieldVal x * certFieldVal y := by
  have h21 : Real.sqrt 21 = Real.sqrt 3 * Real.sqrt 7 := by
    rw [show (21 : ℝ) = 3 * 7 by norm_num, Real.sqrt_mul (by norm_num)]
  have h3' : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h7' : (Real.sqrt 7) ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  simp only [certFieldVal, certFieldMul, h21]
  push_cast
  ring_nf
  rw [h3', h7']
  ring

lemma cfw_rat (q : ℚ) : certFieldVal (lowerHistoryRat q) = (q : ℝ) := by
  simp only [lowerHistoryRat, certFieldVal]
  push_cast
  ring

-- Continuant bookkeeping for the Moebius recursion behind `lowerHistoryCF`.
abbrev CFW := (ℕ × ℕ) × (ℕ × ℕ)

def cfwStep (m : CFW) (a : ℕ+) : CFW :=
  ((m.1.2, m.1.1 + (a : ℕ) * m.1.2), (m.2.2, m.2.1 + (a : ℕ) * m.2.2))

def cfwNum (m : CFW) (Z : ℝ) : ℝ := (m.1.1 : ℝ) * Z + (m.1.2 : ℝ)
def cfwDen (m : CFW) (Z : ℝ) : ℝ := (m.2.1 : ℝ) * Z + (m.2.2 : ℝ)
noncomputable def cfwVal (m : CFW) (Z : ℝ) : ℝ := cfwNum m Z / cfwDen m Z

-- `lowerHistoryMatrix` folds the step over the digit list, but the ascription
-- `(a : ℕ)` in its body does not pin the lambda binder, so the elaborated fold runs
-- over `List ℕ` obtained by coercing the digits. `List.foldl_map` converts that back
-- to a fold over the original `List ℕ+`.
--
-- The bridge needs three steps: `simp` normalises the coercion's monadic bind into
-- `List.flatMap (fun a => [↑a])`, `← List.map_eq_flatMap` turns that into
-- `List.map (fun a => (a : ℕ))`, and `List.foldl_map` moves the fold back onto `w`.
-- The final `rfl` is definitional: `cfwStep` unfolds to exactly the lambda
-- `List.foldl_map` leaves behind.
lemma lowerHistoryMatrix_eq (w : List ℕ+) :
    lowerHistoryMatrix w = w.foldl cfwStep ((1, 0), (0, 1)) := by
  simp only [lowerHistoryMatrix]
  simp [← List.map_eq_flatMap, List.foldl_map]
  rfl

-- The identity matrix evaluates to the identity map.
lemma cfwVal_id (X : ℝ) : cfwVal ((1, 0), (0, 1)) X = X := by
  simp only [cfwVal, cfwNum, cfwDen]
  norm_num

-- The second continuant of a stepped state stays positive: digits are positive.
lemma cfwStep_den_pos {m : CFW} (hm : 0 < m.2.2) (a : ℕ+) : 0 < (cfwStep m a).2.2 := by
  have h : 0 < (a : ℕ) * m.2.2 := Nat.mul_pos a.2 hm
  show 0 < m.2.1 + (a : ℕ) * m.2.2
  omega

lemma fold_den_pos (w : List ℕ+) (m : CFW) (hm : 0 < m.2.2) :
    0 < (w.foldl cfwStep m).2.2 := by
  induction w generalizing m with
  | nil => exact hm
  | cons a w ih => rw [List.foldl_cons]; exact ih (cfwStep m a) (cfwStep_den_pos hm a)

-- The denominator of the value is positive on the admissible region.
lemma cfwDen_pos {m : CFW} (hm : 0 < m.2.2) {Z : ℝ} (hZ : 0 ≤ Z) : 0 < cfwDen m Z := by
  have h1 : (0 : ℝ) ≤ (m.2.1 : ℝ) := by positivity
  have h2 : (0 : ℝ) < (m.2.2 : ℝ) := by exact_mod_cast hm
  have h3 : (0 : ℝ) ≤ (m.2.1 : ℝ) * Z := mul_nonneg h1 hZ
  simp only [cfwDen]
  linarith

-- `prefixEval` stays nonnegative on the nonnegative half-line.
lemma prefixEval_nonneg {Z : ℝ} (hZ : 0 ≤ Z) (w : List ℕ+) : 0 ≤ prefixEval w Z := by
  induction w with
  | nil => exact hZ
  | cons a w ih =>
      have ha : (0 : ℝ) < (a : ℕ) := by exact_mod_cast a.2
      have hpos : 0 < ((a : ℕ) : ℝ) + prefixEval w Z := by linarith
      change 0 ≤ 1 / (((a : ℕ) : ℝ) + prefixEval w Z)
      exact div_nonneg zero_le_one (le_of_lt hpos)

-- One Moebius step.
lemma cfwNum_step (m : CFW) (a : ℕ+) (Y : ℝ) (hne : ((a : ℕ) : ℝ) + Y ≠ 0) :
    cfwNum (cfwStep m a) Y = (((a : ℕ) : ℝ) + Y) * cfwNum m (1 / (((a : ℕ) : ℝ) + Y)) := by
  simp only [cfwNum, cfwStep]
  push_cast
  field_simp
  ring

lemma cfwDen_step (m : CFW) (a : ℕ+) (Y : ℝ) (hne : ((a : ℕ) : ℝ) + Y ≠ 0) :
    cfwDen (cfwStep m a) Y = (((a : ℕ) : ℝ) + Y) * cfwDen m (1 / (((a : ℕ) : ℝ) + Y)) := by
  simp only [cfwDen, cfwStep]
  push_cast
  field_simp
  ring

lemma cfwVal_step (m : CFW) (a : ℕ+) (Y : ℝ) (hm : 0 < m.2.2) (hY : 0 ≤ Y) :
    cfwVal (cfwStep m a) Y = cfwVal m (1 / (((a : ℕ) : ℝ) + Y)) := by
  have ha : (0 : ℝ) < (a : ℕ) := by exact_mod_cast a.2
  have hpos : 0 < ((a : ℕ) : ℝ) + Y := by linarith
  have hne : ((a : ℕ) : ℝ) + Y ≠ 0 := ne_of_gt hpos
  have hY' : 0 ≤ 1 / (((a : ℕ) : ℝ) + Y) := div_nonneg zero_le_one (le_of_lt hpos)
  have hd1 : cfwDen (cfwStep m a) Y ≠ 0 := ne_of_gt (cfwDen_pos (cfwStep_den_pos hm a) hY)
  have hd2 : cfwDen m (1 / (((a : ℕ) : ℝ) + Y)) ≠ 0 := ne_of_gt (cfwDen_pos hm hY')
  rw [cfwVal, cfwVal, div_eq_div_iff hd1 hd2, cfwNum_step m a Y hne, cfwDen_step m a Y hne]
  ring

-- The fold computes the continued fraction of the digit word.
lemma cfwVal_fold (w : List ℕ+) (m : CFW) (Z : ℝ) (hm : 0 < m.2.2) (hZ : 0 ≤ Z) :
    cfwVal (w.foldl cfwStep m) Z = cfwVal m (prefixEval w Z) := by
  induction w generalizing m with
  | nil => rfl
  | cons a w ih =>
      rw [List.foldl_cons]
      have hY : 0 ≤ prefixEval w Z := prefixEval_nonneg hZ w
      rw [ih (cfwStep m a) (cfwStep_den_pos hm a)]
      rw [cfwVal_step m a (prefixEval w Z) hm hY]
      rfl

theorem solution
    (hinv : ∀ z : CertField, certFieldVal z ≠ 0 → certFieldVal (lowerHistoryInv z) = (certFieldVal z)⁻¹)
    (w : List ℕ+) (z : CertField) (hz : 0 ≤ certFieldVal z) :
    certFieldVal (lowerHistoryCF w z) = prefixEval w (certFieldVal z) := by
  set m : CFW := lowerHistoryMatrix w with hm
  have hM : m = w.foldl cfwStep ((1, 0), (0, 1)) := by rw [hm, lowerHistoryMatrix_eq]
  have hm2 : 0 < m.2.2 := by rw [hM]; exact fold_den_pos w ((1, 0), (0, 1)) (by norm_num)
  have hnum :
      certFieldVal (certFieldAdd (certFieldScale (m.1.1 : ℚ) z) (lowerHistoryRat (m.1.2 : ℚ)))
        = cfwNum m (certFieldVal z) := by
    rw [cfw_add, cfw_scale, cfw_rat]
    simp only [cfwNum]
    push_cast
    ring
  have hden :
      certFieldVal (certFieldAdd (certFieldScale (m.2.1 : ℚ) z) (lowerHistoryRat (m.2.2 : ℚ)))
        = cfwDen m (certFieldVal z) := by
    rw [cfw_add, cfw_scale, cfw_rat]
    simp only [cfwDen]
    push_cast
    ring
  have hden_ne :
      certFieldVal (certFieldAdd (certFieldScale (m.2.1 : ℚ) z) (lowerHistoryRat (m.2.2 : ℚ))) ≠ 0 := by
    rw [hden]
    exact ne_of_gt (cfwDen_pos hm2 hz)
  have hcf : certFieldVal (lowerHistoryCF w z) = cfwVal m (certFieldVal z) := by
    have h1 : lowerHistoryCF w z = lowerHistoryDiv
        (certFieldAdd (certFieldScale (m.1.1 : ℚ) z) (lowerHistoryRat (m.1.2 : ℚ)))
        (certFieldAdd (certFieldScale (m.2.1 : ℚ) z) (lowerHistoryRat (m.2.2 : ℚ))) := by
      simp only [lowerHistoryCF, ← hm]
    rw [h1, lowerHistoryDiv, cfw_mul, hinv _ hden_ne, hnum, hden]
    simp only [cfwVal, div_eq_mul_inv]
  have hfold : cfwVal m (certFieldVal z) = prefixEval w (certFieldVal z) := by
    rw [hM]
    rw [cfwVal_fold w ((1, 0), (0, 1)) (certFieldVal z) (by norm_num) hz, cfwVal_id]
  rw [hcf, hfold]
