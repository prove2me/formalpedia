-- Prove2me | solution 1 for EntanglingOps.BinaryPhase.f_infinity_series_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-09T16:02:50.624987+00:00
-- url     : https://prove2.me/submissions/37517f0b-da23-43b2-aac9-15a57f2b05bf

import Mathlib

set_option autoImplicit false

namespace C691
open Real Finset

noncomputable def pp (k : ℕ) : ℝ := Real.sin (Real.pi / 2 ^ k) ^ 2
noncomputable def ee (k : ℕ) : ℝ := -(pp k * Real.log (pp k) + (1 - pp k) * Real.log (1 - pp k))
noncomputable def tt (k : ℕ) : ℝ := 2 ^ k * ee k

lemma pp_rec (k : ℕ) : pp k = 4 * pp (k+1) * (1 - pp (k+1)) := by
  have h : Real.pi / 2 ^ k = 2 * (Real.pi / 2 ^ (k+1)) := by rw [pow_succ, ← div_div]; ring
  simp only [pp]
  rw [h, Real.sin_two_mul, mul_pow, mul_pow, Real.cos_sq']
  ring

lemma pp_two : pp 2 = 1/2 := by
  simp only [pp]
  rw [show Real.pi / 2 ^ 2 = Real.pi / 4 by norm_num, Real.sin_pi_div_four, div_pow,
    Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

lemma pp_nonneg (k : ℕ) : 0 ≤ pp k := sq_nonneg _
lemma pp_le_one (k : ℕ) : pp k ≤ 1 := Real.sin_sq_le_one _

lemma pp_pos (k : ℕ) : 0 < pp (k+2) ∧ pp (k+2) ≤ 1/2 := by
  have h4 : (4:ℝ) ≤ 2 ^ (k+2) := by
    rw [pow_add]; nlinarith [one_le_pow₀ (show (1:ℝ) ≤ 2 by norm_num) (n := k)]
  have hx0 : 0 < Real.pi / 2 ^ (k+2) := by positivity
  have hx : Real.pi / 2 ^ (k+2) ≤ Real.pi / 4 :=
    div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) h4
  have hs : 0 < Real.sin (Real.pi / 2 ^ (k+2)) :=
    Real.sin_pos_of_pos_of_lt_pi hx0 (by linarith [Real.pi_pos])
  have hc : 0 ≤ Real.cos (2 * (Real.pi / 2 ^ (k+2))) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩
  rw [Real.cos_two_mul] at hc
  have := Real.sin_sq_add_cos_sq (Real.pi / 2 ^ (k+2))
  refine ⟨by simp only [pp]; positivity, by simp only [pp]; nlinarith⟩

lemma step_lo {q P l l' : ℝ} (hrec : P = 4*q*(1-q)) (hq0 : 0 ≤ q) (hq : q ≤ 1/2)
    (hl' : l' ≤ 1/2) (hP : l ≤ P) (h : 4*l'*(1-l') ≤ l) : l' ≤ q := by
  by_contra hc; push_neg at hc
  nlinarith [mul_pos (sub_pos.2 hc) (show 0 < 1 - l' - q by linarith)]

lemma step_hi {q P u u' : ℝ} (hrec : P = 4*q*(1-q)) (hq : q ≤ 1/2) (hu0 : 0 ≤ u')
    (hP : P ≤ u) (h : u ≤ 4*u'*(1-u')) : q ≤ u' := by
  by_contra hc; push_neg at hc
  nlinarith [mul_pos (sub_pos.2 hc) (show 0 < 1 - u' - q by linarith)]

lemma neglog_bounds {x l u a A : ℝ} (n : ℕ) (hl : l ≤ x) (hu : x ≤ u) (hl0 : 0 < l) (hu1 : u < 1)
    (ha : a ≤ (∑ i ∈ Finset.range n, l ^ (i+1) / (i+1)) - l ^ (n+1) / (1 - l))
    (hA : (∑ i ∈ Finset.range n, u ^ (i+1) / (i+1)) + u ^ (n+1) / (1 - u) ≤ A) :
    a ≤ -Real.log (1 - x) ∧ -Real.log (1 - x) ≤ A := by
  have hu0 : 0 < u := by linarith
  have hl' := Real.abs_log_sub_add_sum_range_le (show |l| < 1 by rw [abs_of_pos hl0]; linarith) n
  have hu' := Real.abs_log_sub_add_sum_range_le (show |u| < 1 by rw [abs_of_pos hu0]; linarith) n
  rw [abs_of_pos hl0] at hl'
  rw [abs_of_pos hu0] at hu'
  have h1 : Real.log (1 - x) ≤ Real.log (1 - l) := Real.log_le_log (by linarith) (by linarith)
  have h2 : Real.log (1 - u) ≤ Real.log (1 - x) := Real.log_le_log (by linarith) (by linarith)
  constructor
  · linarith [(abs_le.1 hl').2]
  · linarith [(abs_le.1 hu').1]

lemma Lr (k : ℕ) : Real.log (pp (k+2)) = 2 * Real.log 2 + Real.log (pp (k+3)) + Real.log (1 - pp (k+3)) := by
  have h : pp (k+2) = 4 * pp (k+3) * (1 - pp (k+3)) := pp_rec (k+2)
  have hp : 0 < pp (k+3) ∧ pp (k+3) ≤ 1/2 := pp_pos (k+1)
  rw [h, Real.log_mul (mul_pos (by norm_num) hp.1).ne' (sub_pos.2 (by linarith [hp.2])).ne',
    Real.log_mul (by norm_num) hp.1.ne', show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  push_cast; ring

lemma L2 : Real.log (pp 2) = -Real.log 2 := by rw [pp_two, one_div, Real.log_inv]

lemma tt_eq (k : ℕ) : tt k = 2 ^ k * (pp k * (-Real.log (pp k)) + (1 - pp k) * (-Real.log (1 - pp k))) := by
  simp only [tt, ee]; ring

lemma pp_le4 (k : ℕ) : pp k ≤ 4 * pp (k+1) := by
  have := pp_rec k; have := pp_nonneg (k+1); nlinarith

lemma pp_dec (k : ℕ) : pp (k+3) ≤ pp (k+2) := by
  have r : pp (k+2) = 4 * pp (k+3) * (1 - pp (k+3)) := pp_rec (k+2)
  have h : 0 < pp (k+3) ∧ pp (k+3) ≤ 1/2 := pp_pos (k+1)
  nlinarith

lemma tail_dec (m : ℕ) : pp (m + 13) ≤ pp 12 := by
  induction m with
  | zero => exact pp_dec 10
  | succ n ih => exact le_trans (pp_dec (n+11)) ih

lemma tail_lo (m : ℕ) : pp 12 * (1/4:ℝ) ^ (m+1) ≤ pp (m + 13) := by
  induction m with
  | zero => have := pp_le4 12; simp only [zero_add, pow_one]; linarith
  | succ n ih =>
    have h : pp (n + 13) ≤ 4 * pp (n + 1 + 13) := pp_le4 (n+13)
    rw [pow_succ]; nlinarith

lemma tail_hi (u s : ℝ) (hu : pp 12 ≤ u) (hu1 : u < 1) (hs : 1 ≤ s * (4 * (1 - u))) (hs0 : 0 ≤ s)
    (m : ℕ) : pp (m + 13) ≤ pp 12 * s ^ (m+1) := by
  have tstep : ∀ n : ℕ, pp (n + 13) ≤ s * pp (n + 12) := by
    intro n
    have r : pp (n + 12) = 4 * pp (n + 13) * (1 - pp (n + 13)) := pp_rec (n + 12)
    have hq : pp (n + 13) ≤ u := le_trans (tail_dec n) hu
    have hq0 := pp_nonneg (n + 13)
    have a1 : 4 * (1 - u) * pp (n + 13) ≤ pp (n + 12) := by nlinarith
    have a2 : pp (n + 13) ≤ s * (4 * (1 - u)) * pp (n + 13) := by nlinarith
    have a3 := mul_le_mul_of_nonneg_left a1 hs0
    linarith
  induction m with
  | zero => have := tstep 0; simp only [zero_add, pow_one] at this ⊢; linarith
  | succ n ih =>
    have h : pp (n + 1 + 13) ≤ s * pp (n + 13) := tstep (n + 1)
    have h2 := mul_le_mul_of_nonneg_left ih hs0
    rw [pow_succ]; nlinarith

lemma term_bounds {p q1 q2 Y1 Y2 u : ℝ} (hq1 : 0 < q1) (h1 : q1 ≤ p) (h2 : p ≤ q2) (hpu : p ≤ u)
    (hu : u < 1) (hY1 : Y1 ≤ -Real.log p) (hY2 : -Real.log p ≤ Y2) (hY10 : 0 ≤ Y1) :
    q1 * (Y1 + 1 - u) ≤ -(p * Real.log p + (1 - p) * Real.log (1 - p)) ∧
      -(p * Real.log p + (1 - p) * Real.log (1 - p)) ≤ q2 * (Y2 + 1) := by
  have hp : 0 < p := lt_of_lt_of_le hq1 h1
  have h1p : 0 < 1 - p := by linarith
  have a1 : Real.log (1 - p) ≤ -p := by linarith [Real.log_le_sub_one_of_pos h1p]
  have a2 : -p ≤ (1 - p) * Real.log (1 - p) := by
    have h5 := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos h1p) h1p.le
    have h6 : (1 - p) * (1 - (1 - p)⁻¹) = -p := by
      rw [mul_sub, mul_inv_cancel₀ h1p.ne']; ring
    linarith
  have hlp : 0 ≤ -Real.log p := by linarith [Real.log_nonpos hp.le (by linarith : p ≤ 1)]
  have b1 := mul_le_mul h1 hY1 hY10 hp.le
  have b2 := mul_le_mul h2 hY2 hlp (by linarith)
  have b3 := mul_le_mul_of_nonneg_left (show p ≤ -Real.log (1 - p) by linarith) h1p.le
  have b4 := mul_le_mul (show 1 - u ≤ 1 - p by linarith) h1 hq1.le h1p.le
  constructor <;> linarith

lemma hasSum_aff (r α β : ℝ) (h0 : 0 ≤ r) (h1 : r < 1) :
    HasSum (fun m : ℕ => r ^ (m+1) * (α + β * ((m:ℝ) + 1))) (α * (r / (1 - r)) + β * (r / (1 - r) ^ 2)) := by
  have hg := hasSum_geometric_of_lt_one h0 h1
  have hc := hasSum_coe_mul_geometric_of_norm_lt_one
    (show ‖r‖ < 1 by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1)
  have := (hg.mul_left ((α + β) * r)).add (hc.mul_left (β * r))
  have hr : 1 - r ≠ 0 := by linarith
  have e1 : (fun m : ℕ => r ^ (m+1) * (α + β * ((m:ℝ) + 1))) =
      (fun b : ℕ => (α + β) * r * r ^ b + β * r * ((b:ℝ) * r ^ b)) := by funext m; ring
  have e2 : α * (r / (1 - r)) + β * (r / (1 - r) ^ 2) =
      (α + β) * r * (1 - r)⁻¹ + β * r * (r / (1 - r) ^ 2) := by field_simp; ring
  rw [e1, e2]; exact this

lemma tt_nonneg (k : ℕ) : 0 ≤ tt k := by
  have h1 := Real.negMulLog_nonneg (pp_nonneg k) (pp_le_one k)
  have h2 := Real.negMulLog_nonneg (sub_nonneg.2 (pp_le_one k)) (by linarith [pp_nonneg k] : 1 - pp k ≤ 1)
  simp only [Real.negMulLog_def] at h1 h2
  have : 0 ≤ ee k := by unfold ee; nlinarith
  exact mul_nonneg (by positivity) this

lemma tt_pos (k : ℕ) : 0 < tt (k+2) := by
  have hp := pp_pos k
  have h2 := Real.negMulLog_nonneg (sub_nonneg.2 (pp_le_one (k+2))) (by linarith [hp.1] : 1 - pp (k+2) ≤ 1)
  simp only [Real.negMulLog_def] at h2
  have hl : Real.log (pp (k+2)) < 0 := Real.log_neg hp.1 (by linarith [hp.2])
  have h3 := mul_pos hp.1 (neg_pos.2 hl)
  have : 0 < ee (k+2) := by unfold ee; nlinarith
  exact mul_pos (by positivity) this

lemma tt_one : tt 1 = 0 := by simp [tt, ee, pp, Real.sin_pi_div_two]

lemma tt_two : tt 2 = 4 * Real.log 2 := by
  simp only [tt, ee, pp_two]
  rw [show (1:ℝ) - 1/2 = 1/2 by norm_num, one_div, Real.log_inv]; ring

lemma pb2 : (1/2:ℝ) ≤ pp 2 ∧ pp 2 ≤ 1/2 := ⟨pp_two.symm.le, pp_two.le⟩

lemma pb3 : (1464466094067/10000000000000:ℝ) ≤ pp 3 ∧ pp 3 ≤ (366116523517/2500000000000:ℝ) := by
  have h0 : 0 < pp 3 ∧ pp 3 ≤ 1/2 := pp_pos 1
  have hr : pp 2 = 4 * pp 3 * (1 - pp 3) := pp_rec 2
  have hp := pb2
  exact ⟨step_lo hr h0.1.le h0.2 (by norm_num) hp.1 (by norm_num), step_hi hr h0.2 (by norm_num) hp.2 (by norm_num)⟩

lemma pb4 : (3806023374431/100000000000000:ℝ) ≤ pp 4 ∧ pp 4 ≤ (95150584361/2500000000000:ℝ) := by
  have h0 : 0 < pp 4 ∧ pp 4 ≤ 1/2 := pp_pos 2
  have hr : pp 3 = 4 * pp 4 * (1 - pp 4) := pp_rec 3
  have hp := pb3
  exact ⟨step_lo hr h0.1.le h0.2 (by norm_num) hp.1 (by norm_num), step_hi hr h0.2 (by norm_num) hp.2 (by norm_num)⟩

lemma pb5 : (2401839949591/250000000000000:ℝ) ≤ pp 5 ∧ pp 5 ≤ (1921471959681/200000000000000:ℝ) := by
  have h0 : 0 < pp 5 ∧ pp 5 ≤ 1/2 := pp_pos 3
  have hr : pp 4 = 4 * pp 5 * (1 - pp 5) := pp_rec 4
  have hp := pb4
  exact ⟨step_lo hr h0.1.le h0.2 (by norm_num) hp.1 (by norm_num), step_hi hr h0.2 (by norm_num) hp.2 (by norm_num)⟩

lemma pb6 : (300954582987/125000000000000:ℝ) ≤ pp 6 ∧ pp 6 ≤ (2407636663907/1000000000000000:ℝ) := by
  have h0 : 0 < pp 6 ∧ pp 6 ≤ 1/2 := pp_pos 4
  have hr : pp 5 = 4 * pp 6 * (1 - pp 6) := pp_rec 5
  have hp := pb5
  exact ⟨step_lo hr h0.1.le h0.2 (by norm_num) hp.1 (by norm_num), step_hi hr h0.2 (by norm_num) hp.2 (by norm_num)⟩

lemma pb7 : (6022718974119/10000000000000000:ℝ) ≤ pp 7 ∧ pp 7 ≤ (3011359487079/5000000000000000:ℝ) := by
  have h0 : 0 < pp 7 ∧ pp 7 ≤ 1/2 := pp_pos 5
  have hr : pp 6 = 4 * pp 7 * (1 - pp 7) := pp_rec 6
  have hp := pb6
  exact ⟨step_lo hr h0.1.le h0.2 (by norm_num) hp.1 (by norm_num), step_hi hr h0.2 (by norm_num) hp.2 (by norm_num)⟩

lemma pb8 : (1505906518973/10000000000000000:ℝ) ≤ pp 8 ∧ pp 8 ≤ (752953259493/5000000000000000:ℝ) := by
  have h0 : 0 < pp 8 ∧ pp 8 ≤ 1/2 := pp_pos 6
  have hr : pp 7 = 4 * pp 8 * (1 - pp 8) := pp_rec 7
  have hp := pb7
  exact ⟨step_lo hr h0.1.le h0.2 (by norm_num) hp.1 (by norm_num), step_hi hr h0.2 (by norm_num) hp.2 (by norm_num)⟩

lemma pb9 : (941227010689/25000000000000000:ℝ) ≤ pp 9 ∧ pp 9 ≤ (470613505349/12500000000000000:ℝ) := by
  have h0 : 0 < pp 9 ∧ pp 9 ≤ 1/2 := pp_pos 7
  have hr : pp 8 = 4 * pp 9 * (1 - pp 9) := pp_rec 8
  have hp := pb8
  exact ⟨step_lo hr h0.1.le h0.2 (by norm_num) hp.1 (by norm_num), step_hi hr h0.2 (by norm_num) hp.2 (by norm_num)⟩

lemma pb10 : (470617934969/50000000000000000:ℝ) ≤ pp 10 ∧ pp 10 ≤ (4706179349743/500000000000000000:ℝ) := by
  have h0 : 0 < pp 10 ∧ pp 10 ≤ 1/2 := pp_pos 8
  have hr : pp 9 = 4 * pp 10 * (1 - pp 10) := pp_rec 9
  have hp := pb9
  exact ⟨step_lo hr h0.1.le h0.2 (by norm_num) hp.1 (by norm_num), step_hi hr h0.2 (by norm_num) hp.2 (by norm_num)⟩

lemma pb11 : (2353095211899/1000000000000000000:ℝ) ≤ pp 11 ∧ pp 11 ≤ (235309521193/100000000000000000:ℝ) := by
  have h0 : 0 < pp 11 ∧ pp 11 ≤ 1/2 := pp_pos 9
  have hr : pp 10 = 4 * pp 11 * (1 - pp 11) := pp_rec 10
  have hp := pb10
  exact ⟨step_lo hr h0.1.le h0.2 (by norm_num) hp.1 (by norm_num), step_hi hr h0.2 (by norm_num) hp.2 (by norm_num)⟩

lemma pb12 : (735342686301/1250000000000000000:ℝ) ≤ pp 12 ∧ pp 12 ≤ (5882741490493/10000000000000000000:ℝ) := by
  have h0 : 0 < pp 12 ∧ pp 12 ≤ 1/2 := pp_pos 10
  have hr : pp 11 = 4 * pp 12 * (1 - pp 12) := pp_rec 11
  have hp := pb11
  exact ⟨step_lo hr h0.1.le h0.2 (by norm_num) hp.1 (by norm_num), step_hi hr h0.2 (by norm_num) hp.2 (by norm_num)⟩

lemma mb3 : (1583471779811/10000000000000:ℝ) ≤ -Real.log (1 - pp 3) ∧ -Real.log (1 - pp 3) ≤ (1583471886127/10000000000000:ℝ) :=
  neglog_bounds 9 pb3.1 pb3.2 (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
lemma Lr3 : Real.log (pp 2) = 2 * Real.log 2 + Real.log (pp 3) + Real.log (1 - pp 3) := Lr 0

lemma mb4 : (970086079479/25000000000000:ℝ) ≤ -Real.log (1 - pp 4) ∧ -Real.log (1 - pp 4) ≤ (194017217099/5000000000000:ℝ) :=
  neglog_bounds 6 pb4.1 pb4.2 (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
lemma Lr4 : Real.log (pp 3) = 2 * Real.log 2 + Real.log (pp 4) + Real.log (1 - pp 4) := Lr 1

lemma mb5 : (9653808117551/1000000000000000:ℝ) ≤ -Real.log (1 - pp 5) ∧ -Real.log (1 - pp 5) ≤ (4826904141441/500000000000000:ℝ) :=
  neglog_bounds 4 pb5.1 pb5.2 (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
lemma Lr5 : Real.log (pp 4) = 2 * Real.log 2 + Real.log (pp 5) + Real.log (1 - pp 5) := Lr 2

lemma mb6 : (602634909873/250000000000000:ℝ) ≤ -Real.log (1 - pp 6) ∧ -Real.log (1 - pp 6) ≤ (241053970687/100000000000000:ℝ) :=
  neglog_bounds 3 pb6.1 pb6.2 (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
lemma Lr6 : Real.log (pp 5) = 2 * Real.log 2 + Real.log (pp 6) + Real.log (1 - pp 6) := Lr 3

lemma mb7 : (1204906089073/2000000000000000:ℝ) ≤ -Real.log (1 - pp 7) ∧ -Real.log (1 - pp 7) ≤ (6024534817297/10000000000000000:ℝ) :=
  neglog_bounds 2 pb7.1 pb7.2 (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
lemma Lr7 : Real.log (pp 6) = 2 * Real.log 2 + Real.log (pp 7) + Real.log (1 - pp 7) := Lr 4

lemma mb8 : (1506019872539/10000000000000000:ℝ) ≤ -Real.log (1 - pp 8) ∧ -Real.log (1 - pp 8) ≤ (2941445197/19531250000000:ℝ) :=
  neglog_bounds 2 pb8.1 pb8.2 (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
lemma Lr8 : Real.log (pp 7) = 2 * Real.log 2 + Real.log (pp 8) + Real.log (1 - pp 8) := Lr 5

lemma mb9 : (1882489455041/50000000000000000:ℝ) ≤ -Real.log (1 - pp 9) ∧ -Real.log (1 - pp 9) ≤ (470622365099/12500000000000000:ℝ) :=
  neglog_bounds 2 pb9.1 pb9.2 (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
lemma Lr9 : Real.log (pp 8) = 2 * Real.log 2 + Real.log (pp 9) + Real.log (1 - pp 9) := Lr 6

lemma mb10 : (4706201497397/500000000000000000:ℝ) ≤ -Real.log (1 - pp 10) ∧ -Real.log (1 - pp 10) ≤ (9412402996569/1000000000000000000:ℝ) :=
  neglog_bounds 2 pb10.1 pb10.2 (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
lemma Lr10 : Real.log (pp 9) = 2 * Real.log 2 + Real.log (pp 10) + Real.log (1 - pp 10) := Lr 7

lemma mb11 : (588272418707/250000000000000000:ℝ) ≤ -Real.log (1 - pp 11) ∧ -Real.log (1 - pp 11) ≤ (2353100749001/1000000000000000000:ℝ) :=
  neglog_bounds 1 pb11.1 pb11.2 (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
lemma Lr11 : Real.log (pp 10) = 2 * Real.log 2 + Real.log (pp 11) + Real.log (1 - pp 11) := Lr 8

lemma mb12 : (5882738029741/10000000000000000000:ℝ) ≤ -Real.log (1 - pp 12) ∧ -Real.log (1 - pp 12) ≤ (147068623779/250000000000000000:ℝ) :=
  neglog_bounds 1 pb12.1 pb12.2 (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
lemma Lr12 : Real.log (pp 11) = 2 * Real.log 2 + Real.log (pp 12) + Real.log (1 - pp 12) := Lr 9

lemma yb3 : (3:ℝ) * Real.log 2 - (1583471886127/10000000000000:ℝ) ≤ -Real.log (pp 3) ∧ -Real.log (pp 3) ≤ (3:ℝ) * Real.log 2 - (1583471779811/10000000000000:ℝ) := by
  constructor <;> linarith [L2, Lr3, (mb3).1, (mb3).2]
lemma eb3 : (8:ℝ) * ((1464466094067/10000000000000:ℝ) * ((3:ℝ) * Real.log 2 - (1583471886127/10000000000000:ℝ)) + (1 - (366116523517/2500000000000:ℝ)) * (1583471779811/10000000000000:ℝ)) ≤ tt 3 ∧
    tt 3 ≤ (8:ℝ) * ((366116523517/2500000000000:ℝ) * ((3:ℝ) * Real.log 2 - (1583471779811/10000000000000:ℝ)) + (1 - (1464466094067/10000000000000:ℝ)) * (1583471886127/10000000000000:ℝ)) := by
  have hp := pb3; have hm := mb3; have hy := yb3
  have hb0 : (0:ℝ) ≤ (3:ℝ) * Real.log 2 - (1583471886127/10000000000000:ℝ) := by linarith [Real.log_two_gt_d9]
  have h1 := mul_le_mul hp.1 hy.1 hb0 (by linarith [hp.1] : (0:ℝ) ≤ pp 3)
  have h2 := mul_le_mul hp.2 hy.2 (le_trans hb0 hy.1) (by norm_num : (0:ℝ) ≤ (366116523517/2500000000000:ℝ))
  have h3 := mul_le_mul (show 1 - (366116523517/2500000000000:ℝ) ≤ 1 - pp 3 by linarith [hp.2]) hm.1 (by norm_num : (0:ℝ) ≤ (1583471779811/10000000000000:ℝ))
    (by linarith [hp.2] : (0:ℝ) ≤ 1 - pp 3)
  have h4 := mul_le_mul (show 1 - pp 3 ≤ 1 - (1464466094067/10000000000000:ℝ) by linarith [hp.1]) hm.2 (by linarith [hm.1])
    (by norm_num : (0:ℝ) ≤ 1 - (1464466094067/10000000000000:ℝ))
  rw [tt_eq]; constructor <;> linarith [h1, h2, h3, h4]

lemma yb4 : (5:ℝ) * Real.log 2 - (78860252813/400000000000:ℝ) ≤ -Real.log (pp 4) ∧ -Real.log (pp 4) ≤ (5:ℝ) * Real.log 2 - (9857531058013/50000000000000:ℝ) := by
  constructor <;> linarith [L2, Lr3, Lr4, (mb3).1, (mb3).2, (mb4).1, (mb4).2]
lemma eb4 : (16:ℝ) * ((3806023374431/100000000000000:ℝ) * ((5:ℝ) * Real.log 2 - (78860252813/400000000000:ℝ)) + (1 - (95150584361/2500000000000:ℝ)) * (970086079479/25000000000000:ℝ)) ≤ tt 4 ∧
    tt 4 ≤ (16:ℝ) * ((95150584361/2500000000000:ℝ) * ((5:ℝ) * Real.log 2 - (9857531058013/50000000000000:ℝ)) + (1 - (3806023374431/100000000000000:ℝ)) * (194017217099/5000000000000:ℝ)) := by
  have hp := pb4; have hm := mb4; have hy := yb4
  have hb0 : (0:ℝ) ≤ (5:ℝ) * Real.log 2 - (78860252813/400000000000:ℝ) := by linarith [Real.log_two_gt_d9]
  have h1 := mul_le_mul hp.1 hy.1 hb0 (by linarith [hp.1] : (0:ℝ) ≤ pp 4)
  have h2 := mul_le_mul hp.2 hy.2 (le_trans hb0 hy.1) (by norm_num : (0:ℝ) ≤ (95150584361/2500000000000:ℝ))
  have h3 := mul_le_mul (show 1 - (95150584361/2500000000000:ℝ) ≤ 1 - pp 4 by linarith [hp.2]) hm.1 (by norm_num : (0:ℝ) ≤ (970086079479/25000000000000:ℝ))
    (by linarith [hp.2] : (0:ℝ) ≤ 1 - pp 4)
  have h4 := mul_le_mul (show 1 - pp 4 ≤ 1 - (3806023374431/100000000000000:ℝ) by linarith [hp.1]) hm.2 (by linarith [hm.1])
    (by norm_num : (0:ℝ) ≤ 1 - (3806023374431/100000000000000:ℝ))
  rw [tt_eq]; constructor <;> linarith [h1, h2, h3, h4]

lemma yb5 : (7:ℝ) * Real.log 2 - (103402220157691/500000000000000:ℝ) ≤ -Real.log (pp 5) ∧ -Real.log (pp 5) ≤ (7:ℝ) * Real.log 2 - (206804429277811/1000000000000000:ℝ) := by
  constructor <;> linarith [L2, Lr3, Lr4, Lr5, (mb3).1, (mb3).2, (mb4).1, (mb4).2, (mb5).1, (mb5).2]
lemma eb5 : (32:ℝ) * ((2401839949591/250000000000000:ℝ) * ((7:ℝ) * Real.log 2 - (103402220157691/500000000000000:ℝ)) + (1 - (1921471959681/200000000000000:ℝ)) * (9653808117551/1000000000000000:ℝ)) ≤ tt 5 ∧
    tt 5 ≤ (32:ℝ) * ((1921471959681/200000000000000:ℝ) * ((7:ℝ) * Real.log 2 - (206804429277811/1000000000000000:ℝ)) + (1 - (2401839949591/250000000000000:ℝ)) * (4826904141441/500000000000000:ℝ)) := by
  have hp := pb5; have hm := mb5; have hy := yb5
  have hb0 : (0:ℝ) ≤ (7:ℝ) * Real.log 2 - (103402220157691/500000000000000:ℝ) := by linarith [Real.log_two_gt_d9]
  have h1 := mul_le_mul hp.1 hy.1 hb0 (by linarith [hp.1] : (0:ℝ) ≤ pp 5)
  have h2 := mul_le_mul hp.2 hy.2 (le_trans hb0 hy.1) (by norm_num : (0:ℝ) ≤ (1921471959681/200000000000000:ℝ))
  have h3 := mul_le_mul (show 1 - (1921471959681/200000000000000:ℝ) ≤ 1 - pp 5 by linarith [hp.2]) hm.1 (by norm_num : (0:ℝ) ≤ (9653808117551/1000000000000000:ℝ))
    (by linarith [hp.2] : (0:ℝ) ≤ 1 - pp 5)
  have h4 := mul_le_mul (show 1 - pp 5 ≤ 1 - (2401839949591/250000000000000:ℝ) by linarith [hp.1]) hm.2 (by linarith [hm.1])
    (by norm_num : (0:ℝ) ≤ 1 - (2401839949591/250000000000000:ℝ))
  rw [tt_eq]; constructor <;> linarith [h1, h2, h3, h4]

lemma yb6 : (9:ℝ) * Real.log 2 - (52303745005563/250000000000000:ℝ) ≤ -Real.log (pp 6) ∧ -Real.log (pp 6) ≤ (9:ℝ) * Real.log 2 - (209214968917303/1000000000000000:ℝ) := by
  constructor <;> linarith [L2, Lr3, Lr4, Lr5, Lr6, (mb3).1, (mb3).2, (mb4).1, (mb4).2, (mb5).1, (mb5).2, (mb6).1, (mb6).2]
lemma eb6 : (64:ℝ) * ((300954582987/125000000000000:ℝ) * ((9:ℝ) * Real.log 2 - (52303745005563/250000000000000:ℝ)) + (1 - (2407636663907/1000000000000000:ℝ)) * (602634909873/250000000000000:ℝ)) ≤ tt 6 ∧
    tt 6 ≤ (64:ℝ) * ((2407636663907/1000000000000000:ℝ) * ((9:ℝ) * Real.log 2 - (209214968917303/1000000000000000:ℝ)) + (1 - (300954582987/125000000000000:ℝ)) * (241053970687/100000000000000:ℝ)) := by
  have hp := pb6; have hm := mb6; have hy := yb6
  have hb0 : (0:ℝ) ≤ (9:ℝ) * Real.log 2 - (52303745005563/250000000000000:ℝ) := by linarith [Real.log_two_gt_d9]
  have h1 := mul_le_mul hp.1 hy.1 hb0 (by linarith [hp.1] : (0:ℝ) ≤ pp 6)
  have h2 := mul_le_mul hp.2 hy.2 (le_trans hb0 hy.1) (by norm_num : (0:ℝ) ≤ (2407636663907/1000000000000000:ℝ))
  have h3 := mul_le_mul (show 1 - (2407636663907/1000000000000000:ℝ) ≤ 1 - pp 6 by linarith [hp.2]) hm.1 (by norm_num : (0:ℝ) ≤ (602634909873/250000000000000:ℝ))
    (by linarith [hp.2] : (0:ℝ) ≤ 1 - pp 6)
  have h4 := mul_le_mul (show 1 - pp 6 ≤ 1 - (300954582987/125000000000000:ℝ) by linarith [hp.1]) hm.2 (by linarith [hm.1])
    (by norm_num : (0:ℝ) ≤ 1 - (300954582987/125000000000000:ℝ))
  rw [tt_eq]; constructor <;> linarith [h1, h2, h3, h4]

lemma yb7 : (11:ℝ) * Real.log 2 - (2098174335039817/10000000000000000:ℝ) ≤ -Real.log (pp 7) ∧ -Real.log (pp 7) ≤ (11:ℝ) * Real.log 2 - (419634843923679/2000000000000000:ℝ) := by
  constructor <;> linarith [L2, Lr3, Lr4, Lr5, Lr6, Lr7, (mb3).1, (mb3).2, (mb4).1, (mb4).2, (mb5).1, (mb5).2, (mb6).1, (mb6).2, (mb7).1, (mb7).2]
lemma eb7 : (128:ℝ) * ((6022718974119/10000000000000000:ℝ) * ((11:ℝ) * Real.log 2 - (2098174335039817/10000000000000000:ℝ)) + (1 - (3011359487079/5000000000000000:ℝ)) * (1204906089073/2000000000000000:ℝ)) ≤ tt 7 ∧
    tt 7 ≤ (128:ℝ) * ((3011359487079/5000000000000000:ℝ) * ((11:ℝ) * Real.log 2 - (419634843923679/2000000000000000:ℝ)) + (1 - (6022718974119/10000000000000000:ℝ)) * (6024534817297/10000000000000000:ℝ)) := by
  have hp := pb7; have hm := mb7; have hy := yb7
  have hb0 : (0:ℝ) ≤ (11:ℝ) * Real.log 2 - (2098174335039817/10000000000000000:ℝ) := by linarith [Real.log_two_gt_d9]
  have h1 := mul_le_mul hp.1 hy.1 hb0 (by linarith [hp.1] : (0:ℝ) ≤ pp 7)
  have h2 := mul_le_mul hp.2 hy.2 (le_trans hb0 hy.1) (by norm_num : (0:ℝ) ≤ (3011359487079/5000000000000000:ℝ))
  have h3 := mul_le_mul (show 1 - (3011359487079/5000000000000000:ℝ) ≤ 1 - pp 7 by linarith [hp.2]) hm.1 (by norm_num : (0:ℝ) ≤ (1204906089073/2000000000000000:ℝ))
    (by linarith [hp.2] : (0:ℝ) ≤ 1 - pp 7)
  have h4 := mul_le_mul (show 1 - pp 7 ≤ 1 - (6022718974119/10000000000000000:ℝ) by linarith [hp.1]) hm.2 (by linarith [hm.1])
    (by norm_num : (0:ℝ) ≤ 1 - (6022718974119/10000000000000000:ℝ))
  rw [tt_eq]; constructor <;> linarith [h1, h2, h3, h4]

lemma yb8 : (13:ℝ) * Real.log 2 - (2099680354980681/10000000000000000:ℝ) ≤ -Real.log (pp 8) ∧ -Real.log (pp 8) ≤ (13:ℝ) * Real.log 2 - (1049840119745467/5000000000000000:ℝ) := by
  constructor <;> linarith [L2, Lr3, Lr4, Lr5, Lr6, Lr7, Lr8, (mb3).1, (mb3).2, (mb4).1, (mb4).2, (mb5).1, (mb5).2, (mb6).1, (mb6).2, (mb7).1, (mb7).2, (mb8).1, (mb8).2]
lemma eb8 : (256:ℝ) * ((1505906518973/10000000000000000:ℝ) * ((13:ℝ) * Real.log 2 - (2099680354980681/10000000000000000:ℝ)) + (1 - (752953259493/5000000000000000:ℝ)) * (1506019872539/10000000000000000:ℝ)) ≤ tt 8 ∧
    tt 8 ≤ (256:ℝ) * ((752953259493/5000000000000000:ℝ) * ((13:ℝ) * Real.log 2 - (1049840119745467/5000000000000000:ℝ)) + (1 - (1505906518973/10000000000000000:ℝ)) * (2941445197/19531250000000:ℝ)) := by
  have hp := pb8; have hm := mb8; have hy := yb8
  have hb0 : (0:ℝ) ≤ (13:ℝ) * Real.log 2 - (2099680354980681/10000000000000000:ℝ) := by linarith [Real.log_two_gt_d9]
  have h1 := mul_le_mul hp.1 hy.1 hb0 (by linarith [hp.1] : (0:ℝ) ≤ pp 8)
  have h2 := mul_le_mul hp.2 hy.2 (le_trans hb0 hy.1) (by norm_num : (0:ℝ) ≤ (752953259493/5000000000000000:ℝ))
  have h3 := mul_le_mul (show 1 - (752953259493/5000000000000000:ℝ) ≤ 1 - pp 8 by linarith [hp.2]) hm.1 (by norm_num : (0:ℝ) ≤ (1506019872539/10000000000000000:ℝ))
    (by linarith [hp.2] : (0:ℝ) ≤ 1 - pp 8)
  have h4 := mul_le_mul (show 1 - pp 8 ≤ 1 - (1505906518973/10000000000000000:ℝ) by linarith [hp.1]) hm.2 (by linarith [hm.1])
    (by norm_num : (0:ℝ) ≤ 1 - (1505906518973/10000000000000000:ℝ))
  rw [tt_eq]; constructor <;> linarith [h1, h2, h3, h4]

lemma yb9 : (15:ℝ) * Real.log 2 - (10500284264363801/50000000000000000:ℝ) ≤ -Real.log (pp 9) ∧ -Real.log (pp 9) ≤ (15:ℝ) * Real.log 2 - (10500283686909711/50000000000000000:ℝ) := by
  constructor <;> linarith [L2, Lr3, Lr4, Lr5, Lr6, Lr7, Lr8, Lr9, (mb3).1, (mb3).2, (mb4).1, (mb4).2, (mb5).1, (mb5).2, (mb6).1, (mb6).2, (mb7).1, (mb7).2, (mb8).1, (mb8).2, (mb9).1, (mb9).2]
lemma eb9 : (512:ℝ) * ((941227010689/25000000000000000:ℝ) * ((15:ℝ) * Real.log 2 - (10500284264363801/50000000000000000:ℝ)) + (1 - (470613505349/12500000000000000:ℝ)) * (1882489455041/50000000000000000:ℝ)) ≤ tt 9 ∧
    tt 9 ≤ (512:ℝ) * ((470613505349/12500000000000000:ℝ) * ((15:ℝ) * Real.log 2 - (10500283686909711/50000000000000000:ℝ)) + (1 - (941227010689/25000000000000000:ℝ)) * (470622365099/12500000000000000:ℝ)) := by
  have hp := pb9; have hm := mb9; have hy := yb9
  have hb0 : (0:ℝ) ≤ (15:ℝ) * Real.log 2 - (10500284264363801/50000000000000000:ℝ) := by linarith [Real.log_two_gt_d9]
  have h1 := mul_le_mul hp.1 hy.1 hb0 (by linarith [hp.1] : (0:ℝ) ≤ pp 9)
  have h2 := mul_le_mul hp.2 hy.2 (le_trans hb0 hy.1) (by norm_num : (0:ℝ) ≤ (470613505349/12500000000000000:ℝ))
  have h3 := mul_le_mul (show 1 - (470613505349/12500000000000000:ℝ) ≤ 1 - pp 9 by linarith [hp.2]) hm.1 (by norm_num : (0:ℝ) ≤ (1882489455041/50000000000000000:ℝ))
    (by linarith [hp.2] : (0:ℝ) ≤ 1 - pp 9)
  have h4 := mul_le_mul (show 1 - pp 9 ≤ 1 - (941227010689/25000000000000000:ℝ) by linarith [hp.1]) hm.2 (by linarith [hm.1])
    (by norm_num : (0:ℝ) ≤ 1 - (941227010689/25000000000000000:ℝ))
  rw [tt_eq]; constructor <;> linarith [h1, h2, h3, h4]

lemma yb10 : (17:ℝ) * Real.log 2 - (210015097690272589/1000000000000000000:ℝ) ≤ -Real.log (pp 10) ∧ -Real.log (pp 10) ≤ (17:ℝ) * Real.log 2 - (105007543070594507/500000000000000000:ℝ) := by
  constructor <;> linarith [L2, Lr3, Lr4, Lr5, Lr6, Lr7, Lr8, Lr9, Lr10, (mb3).1, (mb3).2, (mb4).1, (mb4).2, (mb5).1, (mb5).2, (mb6).1, (mb6).2, (mb7).1, (mb7).2, (mb8).1, (mb8).2, (mb9).1, (mb9).2, (mb10).1, (mb10).2]
lemma eb10 : (1024:ℝ) * ((470617934969/50000000000000000:ℝ) * ((17:ℝ) * Real.log 2 - (210015097690272589/1000000000000000000:ℝ)) + (1 - (4706179349743/500000000000000000:ℝ)) * (4706201497397/500000000000000000:ℝ)) ≤ tt 10 ∧
    tt 10 ≤ (1024:ℝ) * ((4706179349743/500000000000000000:ℝ) * ((17:ℝ) * Real.log 2 - (105007543070594507/500000000000000000:ℝ)) + (1 - (470617934969/50000000000000000:ℝ)) * (9412402996569/1000000000000000000:ℝ)) := by
  have hp := pb10; have hm := mb10; have hy := yb10
  have hb0 : (0:ℝ) ≤ (17:ℝ) * Real.log 2 - (210015097690272589/1000000000000000000:ℝ) := by linarith [Real.log_two_gt_d9]
  have h1 := mul_le_mul hp.1 hy.1 hb0 (by linarith [hp.1] : (0:ℝ) ≤ pp 10)
  have h2 := mul_le_mul hp.2 hy.2 (le_trans hb0 hy.1) (by norm_num : (0:ℝ) ≤ (4706179349743/500000000000000000:ℝ))
  have h3 := mul_le_mul (show 1 - (4706179349743/500000000000000000:ℝ) ≤ 1 - pp 10 by linarith [hp.2]) hm.1 (by norm_num : (0:ℝ) ≤ (4706201497397/500000000000000000:ℝ))
    (by linarith [hp.2] : (0:ℝ) ≤ 1 - pp 10)
  have h4 := mul_le_mul (show 1 - pp 10 ≤ 1 - (470617934969/50000000000000000:ℝ) by linarith [hp.1]) hm.2 (by linarith [hm.1])
    (by norm_num : (0:ℝ) ≤ 1 - (470617934969/50000000000000000:ℝ))
  rw [tt_eq]; constructor <;> linarith [h1, h2, h3, h4]

lemma yb11 : (19:ℝ) * Real.log 2 - (21001745079102159/100000000000000000:ℝ) ≤ -Real.log (pp 11) ∧ -Real.log (pp 11) ≤ (19:ℝ) * Real.log 2 - (105008719615431921/500000000000000000:ℝ) := by
  constructor <;> linarith [L2, Lr3, Lr4, Lr5, Lr6, Lr7, Lr8, Lr9, Lr10, Lr11, (mb3).1, (mb3).2, (mb4).1, (mb4).2, (mb5).1, (mb5).2, (mb6).1, (mb6).2, (mb7).1, (mb7).2, (mb8).1, (mb8).2, (mb9).1, (mb9).2, (mb10).1, (mb10).2, (mb11).1, (mb11).2]
lemma eb11 : (2048:ℝ) * ((2353095211899/1000000000000000000:ℝ) * ((19:ℝ) * Real.log 2 - (21001745079102159/100000000000000000:ℝ)) + (1 - (235309521193/100000000000000000:ℝ)) * (588272418707/250000000000000000:ℝ)) ≤ tt 11 ∧
    tt 11 ≤ (2048:ℝ) * ((235309521193/100000000000000000:ℝ) * ((19:ℝ) * Real.log 2 - (105008719615431921/500000000000000000:ℝ)) + (1 - (2353095211899/1000000000000000000:ℝ)) * (2353100749001/1000000000000000000:ℝ)) := by
  have hp := pb11; have hm := mb11; have hy := yb11
  have hb0 : (0:ℝ) ≤ (19:ℝ) * Real.log 2 - (21001745079102159/100000000000000000:ℝ) := by linarith [Real.log_two_gt_d9]
  have h1 := mul_le_mul hp.1 hy.1 hb0 (by linarith [hp.1] : (0:ℝ) ≤ pp 11)
  have h2 := mul_le_mul hp.2 hy.2 (le_trans hb0 hy.1) (by norm_num : (0:ℝ) ≤ (235309521193/100000000000000000:ℝ))
  have h3 := mul_le_mul (show 1 - (235309521193/100000000000000000:ℝ) ≤ 1 - pp 11 by linarith [hp.2]) hm.1 (by norm_num : (0:ℝ) ≤ (588272418707/250000000000000000:ℝ))
    (by linarith [hp.2] : (0:ℝ) ≤ 1 - pp 11)
  have h4 := mul_le_mul (show 1 - pp 11 ≤ 1 - (2353095211899/1000000000000000000:ℝ) by linarith [hp.1]) hm.2 (by linarith [hm.1])
    (by norm_num : (0:ℝ) ≤ 1 - (2353095211899/1000000000000000000:ℝ))
  rw [tt_eq]; constructor <;> linarith [h1, h2, h3, h4]

lemma yb12 : (21:ℝ) * Real.log 2 - (105009019532758353/500000000000000000:ℝ) ≤ -Real.log (pp 12) ∧ -Real.log (pp 12) ≤ (21:ℝ) * Real.log 2 - (2100180275046668161/10000000000000000000:ℝ) := by
  constructor <;> linarith [L2, Lr3, Lr4, Lr5, Lr6, Lr7, Lr8, Lr9, Lr10, Lr11, Lr12, (mb3).1, (mb3).2, (mb4).1, (mb4).2, (mb5).1, (mb5).2, (mb6).1, (mb6).2, (mb7).1, (mb7).2, (mb8).1, (mb8).2, (mb9).1, (mb9).2, (mb10).1, (mb10).2, (mb11).1, (mb11).2, (mb12).1, (mb12).2]
lemma eb12 : (4096:ℝ) * ((735342686301/1250000000000000000:ℝ) * ((21:ℝ) * Real.log 2 - (105009019532758353/500000000000000000:ℝ)) + (1 - (5882741490493/10000000000000000000:ℝ)) * (5882738029741/10000000000000000000:ℝ)) ≤ tt 12 ∧
    tt 12 ≤ (4096:ℝ) * ((5882741490493/10000000000000000000:ℝ) * ((21:ℝ) * Real.log 2 - (2100180275046668161/10000000000000000000:ℝ)) + (1 - (735342686301/1250000000000000000:ℝ)) * (147068623779/250000000000000000:ℝ)) := by
  have hp := pb12; have hm := mb12; have hy := yb12
  have hb0 : (0:ℝ) ≤ (21:ℝ) * Real.log 2 - (105009019532758353/500000000000000000:ℝ) := by linarith [Real.log_two_gt_d9]
  have h1 := mul_le_mul hp.1 hy.1 hb0 (by linarith [hp.1] : (0:ℝ) ≤ pp 12)
  have h2 := mul_le_mul hp.2 hy.2 (le_trans hb0 hy.1) (by norm_num : (0:ℝ) ≤ (5882741490493/10000000000000000000:ℝ))
  have h3 := mul_le_mul (show 1 - (5882741490493/10000000000000000000:ℝ) ≤ 1 - pp 12 by linarith [hp.2]) hm.1 (by norm_num : (0:ℝ) ≤ (5882738029741/10000000000000000000:ℝ))
    (by linarith [hp.2] : (0:ℝ) ≤ 1 - pp 12)
  have h4 := mul_le_mul (show 1 - pp 12 ≤ 1 - (735342686301/1250000000000000000:ℝ) by linarith [hp.1]) hm.2 (by linarith [hm.1])
    (by norm_num : (0:ℝ) ≤ 1 - (735342686301/1250000000000000000:ℝ))
  rw [tt_eq]; constructor <;> linarith [h1, h2, h3, h4]

lemma ls : 2 * Real.log 2 - (147068623779/250000000000000000:ℝ) ≤ -Real.log (2500000000000000000/9999994117258509507:ℝ) := by
  have h4 : Real.log (4 * (1 - (5882741490493/10000000000000000000:ℝ))) = 2 * Real.log 2 + Real.log (1 - (5882741490493/10000000000000000000:ℝ)) := by
    rw [Real.log_mul (by norm_num) (by norm_num), show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hS : (2500000000000000000/9999994117258509507:ℝ) = (4 * (1 - (5882741490493/10000000000000000000:ℝ)))⁻¹ := by norm_num
  have h5 := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < 1 - (5882741490493/10000000000000000000:ℝ) by norm_num)
  have h6 : (1:ℝ) - (1 - (5882741490493/10000000000000000000:ℝ))⁻¹ ≥ -(147068623779/250000000000000000:ℝ) := by norm_num
  rw [hS, Real.log_inv, neg_neg, h4]; linarith

lemma tail_term (m : ℕ) :
    (1/2:ℝ) ^ (m+1) * ((2^12:ℝ) * (735342686301/1250000000000000000:ℝ) * ((21:ℝ) * Real.log 2 - (105009019532758353/500000000000000000:ℝ) + 1 - (5882741490493/10000000000000000000:ℝ)) + (2^12:ℝ) * (735342686301/1250000000000000000:ℝ) * (2 * Real.log 2 - (147068623779/250000000000000000:ℝ)) * ((m:ℝ) + 1)) ≤ tt (m + 13) ∧
    tt (m + 13) ≤ (5000000000000000000/9999994117258509507:ℝ) ^ (m+1) * ((2^12:ℝ) * (5882741490493/10000000000000000000:ℝ) * ((21:ℝ) * Real.log 2 - (2100180275046668161/10000000000000000000:ℝ) + 1) + (2^12:ℝ) * (5882741490493/10000000000000000000:ℝ) * (2 * Real.log 2) * ((m:ℝ) + 1)) := by
  have hc := pb12; have hy := yb12
  have hc0 : 0 < pp 12 := lt_of_lt_of_le (by norm_num) hc.1
  have hlo := tail_lo m
  have hhi : pp (m + 13) ≤ pp 12 * (2500000000000000000/9999994117258509507:ℝ) ^ (m+1) := tail_hi (5882741490493/10000000000000000000:ℝ) (2500000000000000000/9999994117258509507:ℝ) hc.2 (by norm_num) (by norm_num) (by norm_num) m
  have hpu : pp (m + 13) ≤ (5882741490493/10000000000000000000:ℝ) := le_trans (tail_dec m) hc.2
  have hq1 : 0 < pp 12 * (1/4:ℝ) ^ (m+1) := by positivity
  have hp0 : 0 < pp (m + 13) := lt_of_lt_of_le hq1 hlo
  have hm0 : (0:ℝ) ≤ (m:ℝ) + 1 := by positivity
  have hl4 : Real.log (1/4 : ℝ) = -(2 * Real.log 2) := by
    rw [one_div, Real.log_inv, show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hlog1 : -Real.log (pp (m + 13)) ≤ -Real.log (pp 12) + ((m:ℝ) + 1) * (2 * Real.log 2) := by
    have := Real.log_le_log hq1 hlo
    rw [Real.log_mul hc0.ne' (by positivity), Real.log_pow, hl4] at this
    push_cast at this; linarith
  have hlog2 : -Real.log (pp 12) + ((m:ℝ) + 1) * (2 * Real.log 2 - (147068623779/250000000000000000:ℝ)) ≤ -Real.log (pp (m + 13)) := by
    have := Real.log_le_log hp0 hhi
    rw [Real.log_mul hc0.ne' (by positivity), Real.log_pow] at this
    have h1 := mul_le_mul_of_nonneg_left ls hm0
    push_cast at this; linarith
  have hY : (0:ℝ) ≤ -Real.log (pp 12) + ((m:ℝ) + 1) * (2 * Real.log 2 - (147068623779/250000000000000000:ℝ)) := by
    have : (0:ℝ) ≤ ((m:ℝ) + 1) * (2 * Real.log 2 - (147068623779/250000000000000000:ℝ)) :=
      mul_nonneg hm0 (by linarith [Real.log_two_gt_d9])
    linarith [hy.1, Real.log_two_gt_d9]
  have T := term_bounds hq1 hlo hhi hpu (by norm_num) hlog2 hlog1 hY
  have e1 : (2:ℝ) ^ (m + 13) * (pp 12 * (1/4:ℝ) ^ (m+1)) = 2 ^ 12 * (1/2:ℝ) ^ (m+1) * pp 12 := by
    rw [show (1/2:ℝ) = 2 * (1/4) by norm_num, mul_pow]; ring
  have e2 : (2:ℝ) ^ (m + 13) * (pp 12 * (2500000000000000000/9999994117258509507:ℝ) ^ (m+1)) = 2 ^ 12 * (5000000000000000000/9999994117258509507:ℝ) ^ (m+1) * pp 12 := by
    rw [show (5000000000000000000/9999994117258509507:ℝ) = 2 * (2500000000000000000/9999994117258509507:ℝ) by norm_num, mul_pow]; ring
  have hG1 : (0:ℝ) < 2 ^ (m + 13) := by positivity
  have hP1 : (0:ℝ) < (1/2:ℝ) ^ (m+1) := by positivity
  have hP2 : (0:ℝ) < (5000000000000000000/9999994117258509507:ℝ) ^ (m+1) := by positivity
  have T1 := mul_le_mul_of_nonneg_left T.1 hG1.le
  have T2 := mul_le_mul_of_nonneg_left T.2 hG1.le
  rw [← mul_assoc, e1] at T1; rw [← mul_assoc, e2] at T2
  have Z1 : (0:ℝ) ≤ (21:ℝ) * Real.log 2 - (105009019532758353/500000000000000000:ℝ) + 1 - (5882741490493/10000000000000000000:ℝ) + ((m:ℝ) + 1) * (2 * Real.log 2 - (147068623779/250000000000000000:ℝ)) := by
    have : (0:ℝ) ≤ ((m:ℝ) + 1) * (2 * Real.log 2 - (147068623779/250000000000000000:ℝ)) :=
      mul_nonneg hm0 (by linarith [Real.log_two_gt_d9])
    linarith [Real.log_two_gt_d9]
  have M1 := mul_le_mul hc.1 (show (21:ℝ) * Real.log 2 - (105009019532758353/500000000000000000:ℝ) + 1 - (5882741490493/10000000000000000000:ℝ) + ((m:ℝ) + 1) * (2 * Real.log 2 - (147068623779/250000000000000000:ℝ)) ≤
      -Real.log (pp 12) + ((m:ℝ) + 1) * (2 * Real.log 2 - (147068623779/250000000000000000:ℝ)) + 1 - (5882741490493/10000000000000000000:ℝ) by linarith [hy.1]) Z1 hc0.le
  have M2 := mul_le_mul hc.2 (show -Real.log (pp 12) + ((m:ℝ) + 1) * (2 * Real.log 2) + 1 ≤
      (21:ℝ) * Real.log 2 - (2100180275046668161/10000000000000000000:ℝ) + ((m:ℝ) + 1) * (2 * Real.log 2) + 1 by linarith [hy.2])
      (by nlinarith [hy.1, Real.log_two_gt_d9, mul_nonneg hm0 (by linarith [Real.log_two_gt_d9] : (0:ℝ) ≤ Real.log 2)]) (by norm_num)
  have M1' := mul_le_mul_of_nonneg_left M1 (by positivity : (0:ℝ) ≤ 2 ^ 12 * (1/2:ℝ) ^ (m+1))
  have M2' := mul_le_mul_of_nonneg_left M2 (by positivity : (0:ℝ) ≤ 2 ^ 12 * (5000000000000000000/9999994117258509507:ℝ) ^ (m+1))
  simp only [tt, ee]; constructor
  · linarith [T1, M1']
  · linarith [T2, M2']

theorem c6 : Summable (fun k : ℕ => tt (k+1)) ∧
    (5.97931:ℝ) * (Real.pi * Real.log 2) < ∑' k : ℕ, tt (k+1) ∧
    ∑' k : ℕ, tt (k+1) < (5.97932:ℝ) * (Real.pi * Real.log 2) := by
  have hgl0 := hasSum_aff (1/2) ((2^12:ℝ) * (735342686301/1250000000000000000:ℝ) * ((21:ℝ) * Real.log 2 - (105009019532758353/500000000000000000:ℝ) + 1 - (5882741490493/10000000000000000000:ℝ))) ((2^12:ℝ) * (735342686301/1250000000000000000:ℝ) * (2 * Real.log 2 - (147068623779/250000000000000000:ℝ))) (by norm_num) (by norm_num)
  have hgu0 := hasSum_aff (5000000000000000000/9999994117258509507:ℝ) ((2^12:ℝ) * (5882741490493/10000000000000000000:ℝ) * ((21:ℝ) * Real.log 2 - (2100180275046668161/10000000000000000000:ℝ) + 1)) ((2^12:ℝ) * (5882741490493/10000000000000000000:ℝ) * (2 * Real.log 2)) (by norm_num) (by norm_num)
  have hgl : HasSum (fun m : ℕ => (1/2:ℝ) ^ (m+1) * (((2^12:ℝ) * (735342686301/1250000000000000000:ℝ) * ((21:ℝ) * Real.log 2 - (105009019532758353/500000000000000000:ℝ) + 1 - (5882741490493/10000000000000000000:ℝ))) + ((2^12:ℝ) * (735342686301/1250000000000000000:ℝ) * (2 * Real.log 2 - (147068623779/250000000000000000:ℝ))) * ((m:ℝ) + 1)))
      (((2^12:ℝ) * (735342686301/1250000000000000000:ℝ) * ((21:ℝ) * Real.log 2 - (105009019532758353/500000000000000000:ℝ) + 1 - (5882741490493/10000000000000000000:ℝ))) + ((2^12:ℝ) * (735342686301/1250000000000000000:ℝ) * (2 * Real.log 2 - (147068623779/250000000000000000:ℝ))) * 2) := by
    have e : ((2^12:ℝ) * (735342686301/1250000000000000000:ℝ) * ((21:ℝ) * Real.log 2 - (105009019532758353/500000000000000000:ℝ) + 1 - (5882741490493/10000000000000000000:ℝ))) * ((1/2:ℝ) / (1 - 1/2)) + ((2^12:ℝ) * (735342686301/1250000000000000000:ℝ) * (2 * Real.log 2 - (147068623779/250000000000000000:ℝ))) * ((1/2:ℝ) / (1 - 1/2) ^ 2) = ((2^12:ℝ) * (735342686301/1250000000000000000:ℝ) * ((21:ℝ) * Real.log 2 - (105009019532758353/500000000000000000:ℝ) + 1 - (5882741490493/10000000000000000000:ℝ))) + ((2^12:ℝ) * (735342686301/1250000000000000000:ℝ) * (2 * Real.log 2 - (147068623779/250000000000000000:ℝ))) * 2 := by ring
    rw [e] at hgl0; exact hgl0
  have hgu : HasSum (fun m : ℕ => (5000000000000000000/9999994117258509507:ℝ) ^ (m+1) * (((2^12:ℝ) * (5882741490493/10000000000000000000:ℝ) * ((21:ℝ) * Real.log 2 - (2100180275046668161/10000000000000000000:ℝ) + 1)) + ((2^12:ℝ) * (5882741490493/10000000000000000000:ℝ) * (2 * Real.log 2)) * ((m:ℝ) + 1)))
      (((2^12:ℝ) * (5882741490493/10000000000000000000:ℝ) * ((21:ℝ) * Real.log 2 - (2100180275046668161/10000000000000000000:ℝ) + 1)) * (5000000000000000000/4999994117258509507:ℝ) + ((2^12:ℝ) * (5882741490493/10000000000000000000:ℝ) * (2 * Real.log 2)) * (49999970586292547535000000000000000000/24999941172619701717443967803209383049:ℝ)) := by
    have e : ((2^12:ℝ) * (5882741490493/10000000000000000000:ℝ) * ((21:ℝ) * Real.log 2 - (2100180275046668161/10000000000000000000:ℝ) + 1)) * ((5000000000000000000/9999994117258509507:ℝ) / (1 - (5000000000000000000/9999994117258509507:ℝ))) + ((2^12:ℝ) * (5882741490493/10000000000000000000:ℝ) * (2 * Real.log 2)) * ((5000000000000000000/9999994117258509507:ℝ) / (1 - (5000000000000000000/9999994117258509507:ℝ)) ^ 2) = ((2^12:ℝ) * (5882741490493/10000000000000000000:ℝ) * ((21:ℝ) * Real.log 2 - (2100180275046668161/10000000000000000000:ℝ) + 1)) * (5000000000000000000/4999994117258509507:ℝ) + ((2^12:ℝ) * (5882741490493/10000000000000000000:ℝ) * (2 * Real.log 2)) * (49999970586292547535000000000000000000/24999941172619701717443967803209383049:ℝ) := by ring
    rw [e] at hgu0; exact hgu0
  have hts : Summable (fun m : ℕ => tt (m + 13)) :=
    Summable.of_nonneg_of_le (fun m => tt_nonneg _) (fun m => (tail_term m).2) hgu.summable
  have hs : Summable (fun k : ℕ => tt (k+1)) := (summable_nat_add_iff 12).mp hts
  have hsplit := hs.sum_add_tsum_nat_add 12
  have hTl := hasSum_le (fun m => (tail_term m).1) hgl hts.hasSum
  have hTu := hasSum_le (fun m => (tail_term m).2) hts.hasSum hgu
  have e : (∑' i : ℕ, tt (i + 12 + 1)) = ∑' m : ℕ, tt (m + 13) := rfl
  have hh : ∑ i ∈ Finset.range 12, tt (i+1) =
      tt 1 + tt 2 + tt 3 + tt 4 + tt 5 + tt 6 + tt 7 + tt 8 + tt 9 + tt 10 + tt 11 + tt 12 := by
    simp [Finset.sum_range_succ]
  have lt2 : (0:ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have pl := mul_lt_mul_of_pos_right Real.pi_lt_d6 lt2
  have pg := mul_lt_mul_of_pos_right Real.pi_gt_d6 lt2
  have l1 := Real.log_two_gt_d9
  have l2 := Real.log_two_lt_d9
  refine ⟨hs, ?_, ?_⟩
  · linarith [hsplit, hh, e, hTl, tt_one, tt_two, eb3.1, eb4.1, eb5.1, eb6.1, eb7.1, eb8.1, eb9.1,
      eb10.1, eb11.1, eb12.1]
  · linarith [hsplit, hh, e, hTu, tt_one, tt_two, eb3.2, eb4.2, eb5.2, eb6.2, eb7.2, eb8.2, eb9.2,
      eb10.2, eb11.2, eb12.2]

end C691

theorem solution (T : ℕ → ℝ)
    (hT : ∀ k : ℕ, T k = (2 : ℝ) ^ k * -(Real.cos (Real.pi / 2 ^ k) ^ 2 *
        Real.logb 2 (Real.cos (Real.pi / 2 ^ k) ^ 2) +
      Real.sin (Real.pi / 2 ^ k) ^ 2 * Real.logb 2 (Real.sin (Real.pi / 2 ^ k) ^ 2))) :
    Summable (fun k : ℕ => T (k + 1)) ∧
    (∀ N : ℕ, ∑ k ∈ Finset.Icc 1 N, T k < ∑' k : ℕ, T (k + 1)) ∧
    (5.97931 : ℝ) < (1 / Real.pi) * ∑' k : ℕ, T (k + 1) ∧
    (1 / Real.pi) * ∑' k : ℕ, T (k + 1) < 5.97932 := by
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hTt : ∀ k, T k = C691.tt k / Real.log 2 := by
    intro k
    rw [hT k, Real.cos_sq']
    simp only [Real.logb, C691.tt, C691.ee, C691.pp, div_eq_mul_inv]
    ring
  have hfun : (fun k : ℕ => T (k + 1)) = fun k => C691.tt (k + 1) / Real.log 2 :=
    funext fun k => hTt (k + 1)
  obtain ⟨hs, hlo, hhi⟩ := C691.c6
  have hsT : Summable (fun k : ℕ => T (k + 1)) := by rw [hfun]; exact hs.div_const _
  have htsum : ∑' k : ℕ, T (k + 1) = (∑' k : ℕ, C691.tt (k + 1)) / Real.log 2 := by
    rw [hfun, tsum_div_const]
  have hpi := Real.pi_pos
  have hnn : ∀ k, 0 ≤ T k := fun k => by rw [hTt]; exact div_nonneg (C691.tt_nonneg k) hl2.le
  have hre : (1 / Real.pi) * ((∑' k : ℕ, C691.tt (k + 1)) / Real.log 2) =
      (∑' k : ℕ, C691.tt (k + 1)) / (Real.pi * Real.log 2) := by ring
  refine ⟨hsT, ?_, ?_, ?_⟩
  · intro N
    have hIcc : ∑ k ∈ Finset.Icc 1 N, T k = ∑ i ∈ Finset.range N, T (i + 1) := by
      induction N with
      | zero => simp
      | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]
    have hsplit := hsT.sum_add_tsum_nat_add N
    have hsN : Summable (fun i : ℕ => T (i + N + 1)) :=
      (summable_nat_add_iff (f := fun k => T (k + 1)) N).mpr hsT
    have hpos : 0 < ∑' i : ℕ, T (i + N + 1) := by
      refine hsN.tsum_pos (fun i => hnn _) 1 ?_
      rw [show 1 + N + 1 = N + 2 by omega, hTt]
      exact div_pos (C691.tt_pos N) hl2
    linarith
  · rw [htsum, hre, lt_div_iff₀ (by positivity)]
    exact hlo
  · rw [htsum, hre, div_lt_iff₀ (by positivity)]
    exact hhi
