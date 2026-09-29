-- Prove2me | solution 2 for Freiman.lowerHistory_pull_from_mobius
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-13T06:57:02.86297+00:00
-- url     : https://prove2.me/submissions/1b8fa963-5c8f-40d5-8914-6dd00da6c21e

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic
import Theorems.Thm_Freiman_continuant_denominator_pos
import Theorems.Thm_Freiman_lowerEarlyTerminal_ratio_append
import Theorems.Thm_Freiman_prefixEval_mobius

open Freiman

namespace M7PullMobius

private theorem matrix_eq (w : List ℕ+) :
    lowerHistoryMatrix w = wordContinuantData w := by
  simp only [lowerHistoryMatrix, wordContinuantData]
  congr 1
  funext m a
  ext <;> simp [Nat.add_comm]

private theorem cd_eq (w : List ℕ+) :
    lowerCD w = (wordContinuantPrevQ w, wordContinuantQ w) := by
  have h : ∀ (v : List ℕ) (m : (ℕ × ℕ) × (ℕ × ℕ)),
      (v.foldl (fun d a => ((d.1.2, (a : ℕ) * d.1.2 + d.1.1),
        (d.2.2, (a : ℕ) * d.2.2 + d.2.1))) m).2 =
      v.foldl (fun z a => (z.2, z.1 + (a : ℕ) * z.2)) m.2 := by
    intro v
    induction v with
    | nil => intro m; rfl
    | cons a v ih =>
      intro m
      simp only [List.foldl_cons]
      rw [ih]
      simp only [Nat.add_comm]
  simpa [lowerCD, wordContinuantPrevQ, wordContinuantQ, wordContinuantData]
    using (h (w.flatMap fun a => [(a : ℕ)]) ((1,0),(0,1))).symm

private theorem q_pos (w : List ℕ+) : 0 < ((lowerCD w).2 : ℝ) := by
  rw [cd_eq]
  exact_mod_cast continuant_denominator_pos w

private theorem lowerScale_pos (base : LowerPair) : 0 < lowerScale base := by
  unfold lowerScale
  exact div_pos (sq_pos_of_pos (q_pos base.1)) (sq_pos_of_pos (q_pos base.2))

private theorem ratio_nonneg (w : List ℕ+) : 0 ≤ lowerRatio w := by
  unfold lowerRatio
  positivity

private theorem matrix_snoc (w : List ℕ+) (a : ℕ+) :
    lowerHistoryMatrix (w ++ [a]) =
      let m := lowerHistoryMatrix w
      ((m.1.2, m.1.1 + (a : ℕ) * m.1.2),
       (m.2.2, m.2.1 + (a : ℕ) * m.2.2)) := by
  rw [matrix_eq, matrix_eq]
  simp [wordContinuantData, List.foldl_append, Nat.add_comm]

private theorem cd_snoc (w : List ℕ+) (a : ℕ+) :
    lowerCD (w ++ [a]) =
      ((lowerCD w).2, (lowerCD w).1 + (a : ℕ) * (lowerCD w).2) := by
  unfold lowerCD
  simp [List.foldl_append]

private theorem append_cd (u w : List ℕ+) :
    let m := lowerHistoryMatrix w
    lowerCD (u ++ w) =
      (m.2.1 * (lowerCD u).2 + m.1.1 * (lowerCD u).1,
       m.2.2 * (lowerCD u).2 + m.1.2 * (lowerCD u).1) := by
  induction w using List.reverseRecOn with
  | nil => simp [lowerHistoryMatrix]
  | append_singleton w a ih =>
      rw [← List.append_assoc, cd_snoc, matrix_snoc]
      simp only
      rw [ih]
      dsimp only
      ext <;> ring

private theorem ratio_append_matrix (u w : List ℕ+) :
    let m := lowerHistoryMatrix w
    lowerRatio (u ++ w) =
      (((m.2.1 : ℕ) : ℝ) + (m.1.1 : ℕ) * lowerRatio u) /
       (((m.2.2 : ℕ) : ℝ) + (m.1.2 : ℕ) * lowerRatio u) := by
  dsimp only
  rw [lowerRatio, append_cd, lowerRatio]
  have hq : ((lowerCD u).2 : ℝ) ≠ 0 := ne_of_gt (q_pos u)
  push_cast
  field_simp

private theorem matrix_k_pos (u w : List ℕ+) :
    let m := lowerHistoryMatrix w
    0 < ((m.2.2 : ℕ) : ℝ) + (m.1.2 : ℕ) * lowerRatio u := by
  dsimp only
  have hd : 0 < (((lowerHistoryMatrix w).2.2 : ℕ) : ℝ) := by
    rw [matrix_eq]
    exact_mod_cast continuant_denominator_pos w
  have hr := ratio_nonneg u
  positivity

private theorem append_den (u w : List ℕ+) :
    let m := lowerHistoryMatrix w
    ((lowerCD (u ++ w)).2 : ℝ) = ((lowerCD u).2 : ℝ) *
      (((m.2.2 : ℕ) : ℝ) + (m.1.2 : ℕ) * lowerRatio u) := by
  dsimp only
  rw [append_cd, lowerRatio]
  have hq : ((lowerCD u).2 : ℝ) ≠ 0 := ne_of_gt (q_pos u)
  push_cast
  field_simp

private theorem prefix_nonneg (w : List ℕ+) (z : ℝ) (hz : 0 ≤ z) :
    0 ≤ prefixEval w z := by
  induction w with
  | nil => exact hz
  | cons a w ih =>
      simp only [prefixEval]
      have ha : (0 : ℝ) < (a : ℕ) := by exact_mod_cast a.pos
      positivity

private theorem matrix_entries (w : List ℕ+) :
    (lowerHistoryMatrix w).1.1 = wordContinuantPrevP w ∧
    (lowerHistoryMatrix w).1.2 = wordContinuantP w ∧
    (lowerHistoryMatrix w).2.1 = wordContinuantPrevQ w ∧
    (lowerHistoryMatrix w).2.2 = wordContinuantQ w := by
  rw [matrix_eq]
  exact ⟨rfl, rfl, rfl, rfl⟩

private theorem factor_pull (u w : List ℕ+) (z : ℝ) (hz : 0 ≤ z) :
    let m := lowerHistoryMatrix w
    (1 + lowerRatio u * prefixEval w z) *
        (((m.2.1 : ℕ) : ℝ) * z + (m.2.2 : ℕ)) =
      (((m.2.2 : ℕ) : ℝ) + (m.1.2 : ℕ) * lowerRatio u) *
        (1 + lowerRatio (u ++ w) * z) := by
  dsimp only
  rw [prefixEval_mobius w z hz, ratio_append_matrix]
  obtain ⟨h11,h12,h21,h22⟩ := matrix_entries w
  simp only [h11,h12,h21,h22]
  have hden : (0 : ℝ) < wordContinuantQ w + z * wordContinuantPrevQ w := by
    have hq : (0 : ℝ) < wordContinuantQ w := by
      exact_mod_cast continuant_denominator_pos w
    positivity
  have hk : (0 : ℝ) < wordContinuantQ w + wordContinuantP w * lowerRatio u := by
    have hq : (0 : ℝ) < wordContinuantQ w := by
      exact_mod_cast continuant_denominator_pos w
    have hr := ratio_nonneg u
    positivity
  have hk' : (0 : ℝ) < wordContinuantQ w + lowerRatio u * wordContinuantP w := by
    nlinarith only [hk]
  field_simp [ne_of_gt hden, ne_of_gt hk, ne_of_gt hk']
  ring

private theorem field_add (x y : CertField) :
    certFieldVal (certFieldAdd x y) = certFieldVal x + certFieldVal y := by
  simp only [certFieldVal, certFieldAdd]
  push_cast
  ring

private theorem field_scale (q : ℚ) (x : CertField) :
    certFieldVal (certFieldScale q x) = (q : ℝ) * certFieldVal x := by
  simp only [certFieldVal, certFieldScale]
  push_cast
  ring

private theorem field_mul (x y : CertField) :
    certFieldVal (certFieldMul x y) = certFieldVal x * certFieldVal y := by
  have h21 : Real.sqrt 21 = Real.sqrt 3 * Real.sqrt 7 := by
    rw [show (21 : ℝ) = 3 * 7 by norm_num, Real.sqrt_mul (by norm_num)]
  have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h7 : (Real.sqrt 7) ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  simp only [certFieldVal, certFieldMul, h21]
  push_cast
  ring_nf
  rw [h3, h7]
  ring

private theorem field_rat (q : ℚ) :
    certFieldVal (lowerHistoryRat q) = (q : ℝ) := by
  simp only [lowerHistoryRat, certFieldVal]
  push_cast
  ring

private theorem fac_value (c d : ℕ) (z : CertField) :
    certFieldVal (certFieldAdd (lowerHistoryRat d) (certFieldScale c z)) =
      (d : ℝ) + (c : ℝ) * certFieldVal z := by
  rw [field_add, field_rat, field_scale]
  norm_cast

private theorem fac_pos (w : List ℕ+) (z : CertField) (hz : 0 ≤ certFieldVal z) :
    let m := lowerHistoryMatrix w
    0 < certFieldVal
      (certFieldAdd (lowerHistoryRat m.2.2) (certFieldScale m.2.1 z)) := by
  dsimp only
  rw [fac_value]
  have hd : 0 < (((lowerHistoryMatrix w).2.2 : ℕ) : ℝ) := by
    rw [matrix_eq]
    exact_mod_cast continuant_denominator_pos w
  positivity

private theorem cf_nonneg
    (hcf : ∀ (w : List ℕ+) (z : CertField), 0 ≤ certFieldVal z →
      certFieldVal (lowerHistoryCF w z) = prefixEval w (certFieldVal z))
    (w : List ℕ+) (z : CertField) (hz : 0 ≤ certFieldVal z) :
    0 ≤ certFieldVal (lowerHistoryCF w z) := by
  rw [hcf w z hz]
  exact prefix_nonneg w _ hz

private theorem sort_factors (c : CertField) (x y : CertField × CertField) (r s : ℝ) :
    certThresholdVal (lowerHistoryThreshold c x y) r s =
      certFieldVal c * (1+s*certFieldVal y.1) * (1+s*certFieldVal y.2) /
        ((1+r*certFieldVal x.1) * (1+r*certFieldVal x.2)) := by
  unfold certThresholdVal certThresholdNum certThresholdDen lowerHistoryThreshold lowerHistorySort
  split_ifs <;> simp only <;> ring

private theorem pull_value_false
    (hcf : ∀ (w : List ℕ+) (z : CertField), 0 ≤ certFieldVal z →
      certFieldVal (lowerHistoryCF w z) = prefixEval w (certFieldVal z))
    (hinv : ∀ z : CertField, certFieldVal z ≠ 0 →
      certFieldVal (lowerHistoryInv z) = (certFieldVal z)⁻¹)
    (base words : LowerPair) (b : CertBound)
    (hc : 0 < certFieldVal b.threshold.c)
    (hx0 : 0 ≤ certFieldVal b.threshold.x0)
    (hx1 : 0 ≤ certFieldVal b.threshold.x1)
    (hy0 : 0 ≤ certFieldVal b.threshold.y0)
    (hy1 : 0 ≤ certFieldVal b.threshold.y1) :
    certThresholdVal (lowerHistoryPull b words false).threshold
        (lowerRatio base.1) (lowerRatio base.2) =
      certThresholdVal b.threshold
          (lowerRatio (base.1 ++ words.1)) (lowerRatio (base.2 ++ words.2)) *
        (((lowerHistoryMatrix words.2).2.2 : ℝ) +
            (lowerHistoryMatrix words.2).1.2 * lowerRatio base.2)^2 /
        (((lowerHistoryMatrix words.1).2.2 : ℝ) +
            (lowerHistoryMatrix words.1).1.2 * lowerRatio base.1)^2 := by
  let tx0 := b.threshold.x0
  let tx1 := b.threshold.x1
  let ty0 := b.threshold.y0
  let ty1 := b.threshold.y1
  let c := b.threshold.c
  let m := lowerHistoryMatrix words.1
  let n := lowerHistoryMatrix words.2
  let fx0 := certFieldAdd (lowerHistoryRat m.2.2) (certFieldScale m.2.1 tx0)
  let fx1 := certFieldAdd (lowerHistoryRat m.2.2) (certFieldScale m.2.1 tx1)
  let fy0 := certFieldAdd (lowerHistoryRat n.2.2) (certFieldScale n.2.1 ty0)
  let fy1 := certFieldAdd (lowerHistoryRat n.2.2) (certFieldScale n.2.1 ty1)
  have hfx0 : 0 < certFieldVal fx0 := by
    simpa [fx0, m, tx0] using fac_pos words.1 b.threshold.x0 hx0
  have hfx1 : 0 < certFieldVal fx1 := by
    simpa [fx1, m, tx1] using fac_pos words.1 b.threshold.x1 hx1
  have hfy0 : 0 < certFieldVal fy0 := by
    simpa [fy0, n, ty0] using fac_pos words.2 b.threshold.y0 hy0
  have hfy1 : 0 < certFieldVal fy1 := by
    simpa [fy1, n, ty1] using fac_pos words.2 b.threshold.y1 hy1
  have hdx : certFieldVal (certFieldMul fx0 fx1) ≠ 0 := by
    rw [field_mul]
    positivity
  have hcoef : certFieldVal (lowerHistoryDiv
      (certFieldMul c (certFieldMul fy0 fy1)) (certFieldMul fx0 fx1)) =
      certFieldVal c * (certFieldVal fy0 * certFieldVal fy1) /
        (certFieldVal fx0 * certFieldVal fx1) := by
    rw [lowerHistoryDiv, field_mul, field_mul, field_mul, hinv _ hdx]
    rw [field_mul]
    simp only [div_eq_mul_inv]
  have hcx0 := hcf words.1 b.threshold.x0 hx0
  have hcx1 := hcf words.1 b.threshold.x1 hx1
  have hcy0 := hcf words.2 b.threshold.y0 hy0
  have hcy1 := hcf words.2 b.threshold.y1 hy1
  have hpx0 := factor_pull base.1 words.1 (certFieldVal b.threshold.x0) hx0
  have hpx1 := factor_pull base.1 words.1 (certFieldVal b.threshold.x1) hx1
  have hpy0 := factor_pull base.2 words.2 (certFieldVal b.threshold.y0) hy0
  have hpy1 := factor_pull base.2 words.2 (certFieldVal b.threshold.y1) hy1
  rw [show (lowerHistoryPull b words false).threshold =
      lowerHistoryThreshold
        (lowerHistoryDiv (certFieldMul c (certFieldMul fy0 fy1))
          (certFieldMul fx0 fx1))
        (lowerHistoryCF words.1 tx0, lowerHistoryCF words.1 tx1)
        (lowerHistoryCF words.2 ty0, lowerHistoryCF words.2 ty1) by
      simp [lowerHistoryPull, c, m, n, fx0, fx1, fy0, fy1, tx0, tx1, ty0, ty1]]
  rw [sort_factors, hcoef]
  simp only [certThresholdVal, certThresholdNum, certThresholdDen]
  simp only [tx0, tx1, ty0, ty1, c] at hcx0 hcx1 hcy0 hcy1 ⊢
  rw [hcx0, hcx1, hcy0, hcy1]
  simp only [fx0, fx1, fy0, fy1, m, n, tx0, tx1, ty0, ty1,
    fac_value] at hfx0 hfx1 hfy0 hfy1 ⊢
  dsimp only at hpx0 hpx1 hpy0 hpy1
  have hkx := matrix_k_pos base.1 words.1
  have hky := matrix_k_pos base.2 words.2
  have hpx0' :
      1 + lowerRatio base.1 * prefixEval words.1 (certFieldVal b.threshold.x0) =
        ((lowerHistoryMatrix words.1).2.2 +
            (lowerHistoryMatrix words.1).1.2 * lowerRatio base.1) *
          (1 + lowerRatio (base.1 ++ words.1) * certFieldVal b.threshold.x0) /
          ((lowerHistoryMatrix words.1).2.2 +
            (lowerHistoryMatrix words.1).2.1 * certFieldVal b.threshold.x0) := by
    apply (eq_div_iff (ne_of_gt hfx0)).2
    nlinarith only [hpx0]
  have hpx1' :
      1 + lowerRatio base.1 * prefixEval words.1 (certFieldVal b.threshold.x1) =
        ((lowerHistoryMatrix words.1).2.2 +
            (lowerHistoryMatrix words.1).1.2 * lowerRatio base.1) *
          (1 + lowerRatio (base.1 ++ words.1) * certFieldVal b.threshold.x1) /
          ((lowerHistoryMatrix words.1).2.2 +
            (lowerHistoryMatrix words.1).2.1 * certFieldVal b.threshold.x1) := by
    apply (eq_div_iff (ne_of_gt hfx1)).2
    nlinarith only [hpx1]
  have hpy0' :
      1 + lowerRatio base.2 * prefixEval words.2 (certFieldVal b.threshold.y0) =
        ((lowerHistoryMatrix words.2).2.2 +
            (lowerHistoryMatrix words.2).1.2 * lowerRatio base.2) *
          (1 + lowerRatio (base.2 ++ words.2) * certFieldVal b.threshold.y0) /
          ((lowerHistoryMatrix words.2).2.2 +
            (lowerHistoryMatrix words.2).2.1 * certFieldVal b.threshold.y0) := by
    apply (eq_div_iff (ne_of_gt hfy0)).2
    nlinarith only [hpy0]
  have hpy1' :
      1 + lowerRatio base.2 * prefixEval words.2 (certFieldVal b.threshold.y1) =
        ((lowerHistoryMatrix words.2).2.2 +
            (lowerHistoryMatrix words.2).1.2 * lowerRatio base.2) *
          (1 + lowerRatio (base.2 ++ words.2) * certFieldVal b.threshold.y1) /
          ((lowerHistoryMatrix words.2).2.2 +
            (lowerHistoryMatrix words.2).2.1 * certFieldVal b.threshold.y1) := by
    apply (eq_div_iff (ne_of_gt hfy1)).2
    nlinarith only [hpy1]
  rw [hpx0', hpx1', hpy0', hpy1']
  field_simp [ne_of_gt hfx0, ne_of_gt hfx1, ne_of_gt hfy0, ne_of_gt hfy1,
    ne_of_gt hkx, ne_of_gt hky]

private theorem pull_normalized_false
    (hcf : ∀ (w : List ℕ+) (z : CertField), 0 ≤ certFieldVal z →
      certFieldVal (lowerHistoryCF w z) = prefixEval w (certFieldVal z))
    (hinv : ∀ z : CertField, certFieldVal z ≠ 0 →
      certFieldVal (lowerHistoryInv z) = (certFieldVal z)⁻¹)
    (base words : LowerPair) (b : CertBound)
    (hc : 0 < certFieldVal b.threshold.c)
    (hx0 : 0 ≤ certFieldVal b.threshold.x0)
    (hx1 : 0 ≤ certFieldVal b.threshold.x1)
    (hy0 : 0 ≤ certFieldVal b.threshold.y0)
    (hy1 : 0 ≤ certFieldVal b.threshold.y1) :
    certThresholdVal (lowerHistoryPull b words false).threshold
        (lowerRatio base.1) (lowerRatio base.2) / lowerScale base =
      certThresholdVal b.threshold
          (lowerRatio (base.1 ++ words.1)) (lowerRatio (base.2 ++ words.2)) /
        lowerScale (lowerHistoryAppend base words) := by
  rw [pull_value_false hcf hinv base words b hc hx0 hx1 hy0 hy1]
  unfold lowerScale lowerHistoryAppend
  rw [append_den base.1 words.1, append_den base.2 words.2]
  have hqx := q_pos base.1
  have hqy := q_pos base.2
  have hkx := matrix_k_pos base.1 words.1
  have hky := matrix_k_pos base.2 words.2
  field_simp [ne_of_gt hqx, ne_of_gt hqy, ne_of_gt hkx, ne_of_gt hky]

private theorem pull_bound_false
    (hcf : ∀ (w : List ℕ+) (z : CertField), 0 ≤ certFieldVal z →
      certFieldVal (lowerHistoryCF w z) = prefixEval w (certFieldVal z))
    (hinv : ∀ z : CertField, certFieldVal z ≠ 0 →
      certFieldVal (lowerHistoryInv z) = (certFieldVal z)⁻¹)
    (base words : LowerPair) (b : CertBound)
    (hc : 0 < certFieldVal b.threshold.c)
    (hx0 : 0 ≤ certFieldVal b.threshold.x0)
    (hx1 : 0 ≤ certFieldVal b.threshold.x1)
    (hy0 : 0 ≤ certFieldVal b.threshold.y0)
    (hy1 : 0 ≤ certFieldVal b.threshold.y1) :
    certBoundHolds b
        (lowerRatio (base.1 ++ words.1)) (lowerRatio (base.2 ++ words.2))
        (lowerScale (lowerHistoryAppend base words)) ↔
      certBoundHolds (lowerHistoryPull b words false)
        (lowerRatio base.1) (lowerRatio base.2) (lowerScale base) := by
  have hn := pull_normalized_false hcf hinv base words b hc hx0 hx1 hy0 hy1
  have hqb := lowerScale_pos base
  have hqa := lowerScale_pos (lowerHistoryAppend base words)
  have hlower : (lowerHistoryPull b words false).lower = b.lower := by
    simp [lowerHistoryPull]
  have hstrict : (lowerHistoryPull b words false).strict = b.strict := by
    simp [lowerHistoryPull]
  unfold certBoundHolds
  rw [hlower, hstrict]
  split <;> split
  · rw [← div_lt_one hqa, ← div_lt_one hqb, hn]
  · rw [← div_le_one hqa, ← div_le_one hqb, hn]
  · rw [← one_lt_div hqa, ← one_lt_div hqb, hn]
  · rw [← one_le_div hqa, ← one_le_div hqb, hn]


end M7PullMobius

open Freiman
namespace M7PullFlip
set_option maxHeartbeats 2000000

private def flipBound (b : CertBound) : CertBound :=
  ⟨!b.lower,b.strict,lowerHistoryThreshold (lowerHistoryInv b.threshold.c)
    (b.threshold.y0,b.threshold.y1) (b.threshold.x0,b.threshold.x1)⟩

private theorem sort_factors (c : CertField) (x y : CertField × CertField) (r s : ℝ) :
    certThresholdVal (lowerHistoryThreshold c x y) r s =
      certFieldVal c * (1+s*certFieldVal y.1) * (1+s*certFieldVal y.2) /
        ((1+r*certFieldVal x.1) * (1+r*certFieldVal x.2)) := by
  unfold certThresholdVal certThresholdNum certThresholdDen lowerHistoryThreshold lowerHistorySort
  split_ifs <;> simp only <;> ring

private theorem fields
    (hinv : ∀ z : CertField, certFieldVal z ≠ 0 →
      certFieldVal (lowerHistoryInv z) = (certFieldVal z)⁻¹)
    (b : CertBound) (hc : 0 < certFieldVal b.threshold.c)
    (hx0 : 0 ≤ certFieldVal b.threshold.x0) (hx1 : 0 ≤ certFieldVal b.threshold.x1)
    (hy0 : 0 ≤ certFieldVal b.threshold.y0) (hy1 : 0 ≤ certFieldVal b.threshold.y1) :
    0 < certFieldVal (flipBound b).threshold.c ∧
      0 ≤ certFieldVal (flipBound b).threshold.x0 ∧
      0 ≤ certFieldVal (flipBound b).threshold.x1 ∧
      0 ≤ certFieldVal (flipBound b).threshold.y0 ∧
      0 ≤ certFieldVal (flipBound b).threshold.y1 := by
  have hi : 0 < certFieldVal (lowerHistoryInv b.threshold.c) := by
    rw [hinv _ (ne_of_gt hc)]
    positivity
  dsimp only [flipBound,lowerHistoryThreshold,lowerHistorySort]
  split_ifs <;> simp_all

private theorem threshold_flip_value
    (hinv : ∀ z : CertField, certFieldVal z ≠ 0 →
      certFieldVal (lowerHistoryInv z) = (certFieldVal z)⁻¹)
    (b : CertBound) (hc : 0 < certFieldVal b.threshold.c) (r s : ℝ) :
    certThresholdVal (flipBound b).threshold r s =
      (certThresholdVal b.threshold s r)⁻¹ := by
  change certThresholdVal (lowerHistoryThreshold (lowerHistoryInv b.threshold.c)
    (b.threshold.y0,b.threshold.y1) (b.threshold.x0,b.threshold.x1)) r s = _
  rw [sort_factors,hinv _ (ne_of_gt hc)]
  simp only [certThresholdVal,certThresholdNum,certThresholdDen,div_eq_mul_inv,
    mul_inv_rev,inv_inv]
  ring

private theorem threshold_pos (b : CertBound) (hc : 0 < certFieldVal b.threshold.c)
    (hx0 : 0 ≤ certFieldVal b.threshold.x0) (hx1 : 0 ≤ certFieldVal b.threshold.x1)
    (hy0 : 0 ≤ certFieldVal b.threshold.y0) (hy1 : 0 ≤ certFieldVal b.threshold.y1)
    (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) : 0 < certThresholdVal b.threshold r s := by
  unfold certThresholdVal certThresholdNum certThresholdDen
  positivity

private theorem bound_flip
    (hinv : ∀ z : CertField, certFieldVal z ≠ 0 →
      certFieldVal (lowerHistoryInv z) = (certFieldVal z)⁻¹)
    (b : CertBound) (hc : 0 < certFieldVal b.threshold.c)
    (hx0 : 0 ≤ certFieldVal b.threshold.x0) (hx1 : 0 ≤ certFieldVal b.threshold.x1)
    (hy0 : 0 ≤ certFieldVal b.threshold.y0) (hy1 : 0 ≤ certFieldVal b.threshold.y1)
    (r s q : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) (hq : 0 < q) :
    certBoundHolds b s r q⁻¹ ↔ certBoundHolds (flipBound b) r s q := by
  have hT := threshold_pos b hc hx0 hx1 hy0 hy1 s r hs hr
  have hflip := threshold_flip_value hinv b hc r s
  unfold certBoundHolds
  rw [hflip]
  have hlow : (flipBound b).lower = !b.lower := rfl
  have hstrict : (flipBound b).strict = b.strict := rfl
  rw [hlow,hstrict]
  cases hl : b.lower <;> cases ht : b.strict <;>
    simp only [hl,ht,Bool.not_false,Bool.not_true,Bool.false_eq_true,if_false,if_true,
      inv_eq_one_div,div_le_iff₀ hq,div_lt_iff₀ hq,le_div_iff₀ hq,lt_div_iff₀ hq,
      div_le_iff₀ hT,div_lt_iff₀ hT,le_div_iff₀ hT,lt_div_iff₀ hT] <;>
    constructor <;> intro h <;> nlinarith

private theorem pull_flip (b : CertBound) (words : LowerPair) :
    lowerHistoryPull b words true = lowerHistoryPull (flipBound b) words false := rfl

end M7PullFlip

-- This assembly fragment follows PullMobius.lean and PullFlip.lean in the
-- standalone submission so their private lemmas remain local to that proof.
open Freiman
namespace M7PullFinish

private theorem compare_normalized (lower strict : Bool) (x y q q' : ℝ)
    (hq : 0 < q) (hq' : 0 < q') (h : x/q = y/q') :
    (if lower then if strict then x<q else x≤q else if strict then q<x else q≤x) ↔
    (if lower then if strict then y<q' else y≤q' else if strict then q'<y else q'≤y) := by
  have hlt : x<q ↔ y<q' := by
    rw [← div_lt_one hq,← div_lt_one hq',h]
  have hle : x≤q ↔ y≤q' := by
    rw [← div_le_one hq,← div_le_one hq',h]
  have hgt : q<x ↔ q'<y := by simpa only [not_le] using not_congr hle
  have hge : q≤x ↔ q'≤y := by simpa only [not_lt] using not_congr hlt
  cases lower <;> cases strict <;> simpa using (by assumption)

private theorem pull_false
    (hcf : ∀ (w : List ℕ+) (z : CertField), 0 ≤ certFieldVal z →
      certFieldVal (lowerHistoryCF w z) = prefixEval w (certFieldVal z))
    (hinv : ∀ z : CertField, certFieldVal z ≠ 0 →
      certFieldVal (lowerHistoryInv z) = (certFieldVal z)⁻¹)
    (base words : LowerPair) (b : CertBound)
    (hc : 0 < certFieldVal b.threshold.c)
    (hx0 : 0 ≤ certFieldVal b.threshold.x0) (hx1 : 0 ≤ certFieldVal b.threshold.x1)
    (hy0 : 0 ≤ certFieldVal b.threshold.y0) (hy1 : 0 ≤ certFieldVal b.threshold.y1) :
    lowerHistoryAtBase (lowerHistoryAppend base words) [b] ↔
      lowerHistoryAtBase base [lowerHistoryPull b words false] := by
  have hval := M7PullMobius.pull_normalized_false hcf hinv base words b hc hx0 hx1 hy0 hy1
  have hq := M7PullMobius.lowerScale_pos base
  have hq' := M7PullMobius.lowerScale_pos (lowerHistoryAppend base words)
  have hlow : (lowerHistoryPull b words false).lower = b.lower := rfl
  have hstrict : (lowerHistoryPull b words false).strict = b.strict := rfl
  have hcomp := compare_normalized b.lower b.strict _ _ _ _ hq hq' hval
  have hcert : certBoundHolds (lowerHistoryPull b words false)
      (lowerRatio base.1) (lowerRatio base.2) (lowerScale base) ↔
      certBoundHolds b (lowerRatio (base.1++words.1)) (lowerRatio (base.2++words.2))
        (lowerScale (lowerHistoryAppend base words)) := by
    simpa only [certBoundHolds,hlow,hstrict] using hcomp
  simpa only [lowerHistoryAtBase,lowerHistoryConditions,List.mem_singleton,forall_eq,
    lowerHistoryAppend] using hcert.symm

private theorem pull_law
    (hcf : ∀ (w : List ℕ+) (z : CertField), 0 ≤ certFieldVal z →
      certFieldVal (lowerHistoryCF w z) = prefixEval w (certFieldVal z))
    (hinv : ∀ z : CertField, certFieldVal z ≠ 0 →
      certFieldVal (lowerHistoryInv z) = (certFieldVal z)⁻¹) : LowerHistoryPullLaw := by
  intro base words b flip hc hx0 hx1 hy0 hy1
  cases flip
  · exact pull_false hcf hinv base words b hc hx0 hx1 hy0 hy1
  · let p := lowerHistoryAppend base words
    have hq := M7PullMobius.lowerScale_pos p
    have hr : 0 ≤ lowerRatio p.1 := M7PullMobius.ratio_nonneg _
    have hs : 0 ≤ lowerRatio p.2 := M7PullMobius.ratio_nonneg _
    have hflip := M7PullFlip.bound_flip hinv b hc hx0 hx1 hy0 hy1
      (lowerRatio p.1) (lowerRatio p.2) (lowerScale p) hr hs hq
    have hswap : lowerScale (lowerHistoryOrient p true) = (lowerScale p)⁻¹ := by
      simp only [lowerHistoryOrient,if_true,lowerScale,inv_div]
    have hactual : lowerHistoryAtBase (lowerHistoryOrient p true) [b] ↔
        lowerHistoryAtBase p [M7PullFlip.flipBound b] := by
      simp only [lowerHistoryAtBase,lowerHistoryConditions,List.mem_singleton,forall_eq]
      rw [hswap]
      exact hflip
    obtain ⟨hc',hx0',hx1',hy0',hy1'⟩ := M7PullFlip.fields hinv b hc hx0 hx1 hy0 hy1
    have hfalse := pull_false hcf hinv base words (M7PullFlip.flipBound b)
      hc' hx0' hx1' hy0' hy1'
    rw [M7PullFlip.pull_flip]
    exact hactual.trans hfalse

end M7PullFinish

open Freiman

theorem solution (hcf : ∀ (w : List ℕ+) (z : CertField), 0 ≤ certFieldVal z → certFieldVal (lowerHistoryCF w z) = prefixEval w (certFieldVal z)) (hinv : ∀ z : CertField, certFieldVal z ≠ 0 → certFieldVal (lowerHistoryInv z) = (certFieldVal z)⁻¹) :
    LowerHistoryPullLaw := by
  exact M7PullFinish.pull_law hcf hinv

#print axioms solution
