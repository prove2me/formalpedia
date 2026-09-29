-- Prove2me | solution 1 for Freiman.lower_bridge_survivor_transfer
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T10:20:08.96166+00:00
-- url     : https://prove2.me/submissions/3895bd20-0bcd-4685-af16-d60a38e9e67b

import Definitions.Def_Freiman_lowerBridgeCatalog
import Mathlib
set_option maxHeartbeats 2000000
noncomputable section
namespace OtherBridge
open Freiman
theorem pe_append : ∀ (u v : List ℕ+) (x : ℝ),
    prefixEval (u ++ v) x = prefixEval u (prefixEval v x)
  | [], v, x => rfl
  | a :: u, v, x => by
      simp only [List.cons_append, prefixEval, pe_append u v x]

theorem wm_eq (w : List ℕ+) : lowerInitialWordMatrix w =
    List.foldl (fun m (d : ℕ) => lowerInitialMatMul m ⟨0,1,1,(d : ℝ)⟩)
      ⟨1,0,0,1⟩ (w.map PNat.val) := by
  have hbind : (do let a ← w; pure (a : ℕ)) = w.map PNat.val := by
    induction w with
    | nil => rfl
    | cons a w ih => simpa using ih
  unfold lowerInitialWordMatrix
  rw [hbind]

theorem wm_append (w : List ℕ+) (a : ℕ+) :
    lowerInitialWordMatrix (w ++ [a])
      = lowerInitialMatMul (lowerInitialWordMatrix w) ⟨0,1,1,((a : ℕ) : ℝ)⟩ := by
  rw [wm_eq, wm_eq, List.map_append, List.foldl_append]
  simp


private theorem mat_assoc (a b c : LowerInitialMatrix) :
    lowerInitialMatMul (lowerInitialMatMul a b) c = lowerInitialMatMul a (lowerInitialMatMul b c) := by
  cases a; cases b; cases c
  unfold lowerInitialMatMul
  congr 1 <;> ring

private theorem wm_append_all (u v : List ℕ+) :
    lowerInitialWordMatrix (u ++ v) =
      lowerInitialMatMul (lowerInitialWordMatrix u) (lowerInitialWordMatrix v) := by
  induction v using List.reverseRecOn with
  | nil => simp [wm_eq, lowerInitialMatMul]
  | append_singleton v a ih =>
      rw [← List.append_assoc, wm_append, ih, wm_append, mat_assoc]

private theorem scale_mul (s : ℝ) (a b : LowerInitialMatrix) :
    lowerInitialMatMul (lowerInitialMatScale s a) b = lowerInitialMatScale s (lowerInitialMatMul a b) := by
  cases a; cases b
  unfold lowerInitialMatScale lowerInitialMatMul
  congr 1 <;> ring

private theorem widthDen_scale (s : ℝ) (a : LowerInitialMatrix) :
    lowerBridgeWidthDen (lowerInitialMatScale s a) = s^2 * lowerBridgeWidthDen a := by
  unfold lowerBridgeWidthDen lowerInitialMatDen lowerInitialMatScale
  ring

private theorem alpha_pos : 0 < lowerAlpha := by
  have hs : Real.sqrt 21 ^ 2 = 21 := Real.sq_sqrt (by norm_num)
  have h := Real.sqrt_nonneg 21
  unfold lowerAlpha
  nlinarith

private theorem gap_pos : 0 < lowerBeta - lowerAlpha := by
  have hs : Real.sqrt 21 ^ 2 = 21 := Real.sq_sqrt (by norm_num)
  have h := Real.sqrt_nonneg 21
  unfold lowerBeta lowerAlpha
  nlinarith

private theorem beta_pos : 0 < lowerBeta := by linarith [alpha_pos, gap_pos]

abbrev FractionProperty : Prop := ∀ (w : List ℕ+) (t : ℝ), 0 < t →
  prefixEval w t = lowerInitialMatEval (lowerInitialWordMatrix w) t ∧
  0 < lowerInitialMatDen (lowerInitialWordMatrix w) t ∧
  (lowerInitialWordMatrix w).a*(lowerInitialWordMatrix w).d -
    (lowerInitialWordMatrix w).b*(lowerInitialWordMatrix w).c = (-1:ℝ)^w.length

private theorem den_pos (hf : FractionProperty) (w : List ℕ+) :
    0 < lowerBridgeWidthDen (lowerInitialWordMatrix w) :=
  mul_pos (hf w _ alpha_pos).2.1 (hf w _ beta_pos).2.1

private theorem cross_diff (a b x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    (a/y-b/x)*(x*y) = a*x-b*y := by
  field_simp
  try ring

private theorem width_formula (hf : FractionProperty) (w : List ℕ+) :
    lowerWidth w = (lowerBeta - lowerAlpha) / lowerBridgeWidthDen (lowerInitialWordMatrix w) := by
  obtain ⟨ha, hda, hdet⟩ := hf w _ alpha_pos
  obtain ⟨hb, hdb, _⟩ := hf w _ beta_pos
  have hdiff : prefixEval w lowerBeta - prefixEval w lowerAlpha =
      ((lowerBeta-lowerAlpha) * (-1:ℝ)^w.length) /
        lowerBridgeWidthDen (lowerInitialWordMatrix w) := by
    apply (eq_div_iff (ne_of_gt (den_pos hf w))).2
    rw [ha, hb]
    unfold lowerInitialMatEval lowerBridgeWidthDen lowerInitialMatDen
    unfold lowerInitialMatDen at hda hdb
    rw [cross_diff _ _ _ _ (ne_of_gt hda) (ne_of_gt hdb), ← hdet]
    ring
  rw [lowerWidth, hdiff, abs_div, abs_mul, abs_of_pos gap_pos,
    abs_pow, abs_neg, abs_one, one_pow, mul_one, abs_of_pos (den_pos hf w)]

private theorem width_reverse (hf : FractionProperty) (u v : List ℕ+) (s : ℝ) (hs : 0 < s)
    (a b : LowerInitialMatrix) (hu : lowerInitialWordMatrix u = lowerInitialMatScale s a)
    (hv : lowerInitialWordMatrix v = lowerInitialMatScale s b)
    (hd : lowerBridgeWidthDen a < lowerBridgeWidthDen b) : lowerWidth v < lowerWidth u := by
  have hdu := den_pos hf u
  have hdv := den_pos hf v
  have hdiff : lowerBridgeWidthDen (lowerInitialWordMatrix u) <
      lowerBridgeWidthDen (lowerInitialWordMatrix v) := by
    rw [hu, hv, widthDen_scale, widthDen_scale]
    exact mul_lt_mul_of_pos_left hd (sq_pos_of_pos hs)
  rw [width_formula hf, width_formula hf]
  apply (div_lt_div_iff₀ hdv hdu).2
  nlinarith [mul_pos gap_pos (sub_pos.mpr hdiff)]

private theorem bridge_link (c : LowerBridgeCase) (n k : ℕ)
    (hm : lowerInitialSeamLink (lowerBridgeSeamCase c) n (lowerBridgeK c k) 0) :
    ∃ s : ℝ, 0 < s ∧
      lowerInitialWordMatrix (lowerBridgePair c n k).1 =
        lowerInitialMatScale s (lowerBridgeMatrices c (lowerInitialX n) (lowerInitialY k)).1 ∧
      lowerInitialWordMatrix (lowerBridgePair c n k).2 =
        lowerInitialMatScale s (lowerBridgeMatrices c (lowerInitialX n) (lowerInitialY k)).2 := by
  have hms : lowerInitialSeamMatrices (lowerBridgeSeamCase c) (lowerInitialX n)
      (lowerInitialY (lowerBridgeK c k)) (lowerInitialY 0) =
      lowerBridgeMatrices c (lowerInitialX n) (lowerInitialY k) := by
    cases c <;> simp [lowerBridgeMatrices, lowerBridgeK, lowerBridgeFamily,
      lowerBridgeSeamCase, lowerInitialSeamFamily, lowerInitialY, lowerInitialV]
  have h := hm.2
  change ∃ s : ℝ, 0 < s ∧
    lowerInitialWordMatrix (lowerBridgePair c n k).1 =
      lowerInitialMatScale s (lowerInitialSeamMatrices (lowerBridgeSeamCase c) (lowerInitialX n)
        (lowerInitialY (lowerBridgeK c k)) (lowerInitialY 0)).1 ∧
    lowerInitialWordMatrix (lowerBridgePair c n k).2 =
      lowerInitialMatScale s (lowerInitialSeamMatrices (lowerBridgeSeamCase c) (lowerInitialX n)
        (lowerInitialY (lowerBridgeK c k)) (lowerInitialY 0)).2 at h
  rwa [hms] at h

end OtherBridge
open Freiman OtherBridge

namespace OtherBridge
theorem cd_eq (w : List ℕ+) : lowerCD w =
    List.foldl (fun z (a : ℕ) => (z.2, z.1 + a * z.2)) (0, 1) (w.map PNat.val) := by
  have hbind : (do let a ← w; pure (a : ℕ)) = w.map PNat.val := by
    induction w with
    | nil => rfl
    | cons a w ih => simpa using ih
  unfold lowerCD
  rw [hbind]

theorem cd_append (w : List ℕ+) (a : ℕ+) :
    lowerCD (w ++ [a]) = ((lowerCD w).2, (lowerCD w).1 + (a : ℕ) * (lowerCD w).2) := by
  rw [cd_eq, cd_eq, List.map_append, List.foldl_append]
  simp

theorem cd_pos : ∀ w : List ℕ+, 0 < (lowerCD w).2 := by
  intro w
  induction w using List.reverseRecOn with
  | nil => rw [cd_eq]; norm_num
  | append_singleton w a ih =>
      rw [cd_append]
      show 0 < (lowerCD w).1 + (a : ℕ) * (lowerCD w).2
      have h1 : 0 < (a : ℕ) * (lowerCD w).2 := Nat.mul_pos a.pos ih
      omega

theorem cd_fib : ∀ w : List ℕ+,
    Nat.fib w.length ≤ (lowerCD w).1 ∧ Nat.fib (w.length + 1) ≤ (lowerCD w).2 := by
  intro w
  induction w using List.reverseRecOn with
  | nil => rw [cd_eq]; norm_num
  | append_singleton w a ih =>
      rw [cd_append]
      have hlen : (w ++ [a]).length = w.length + 1 := by simp
      refine ⟨?_, ?_⟩
      · show Nat.fib (w ++ [a]).length ≤ (lowerCD w).2
        rw [hlen]; exact ih.2
      · show Nat.fib ((w ++ [a]).length + 1) ≤ (lowerCD w).1 + (a : ℕ) * (lowerCD w).2
        rw [hlen, Nat.fib_add_two]
        have h2 : (lowerCD w).2 ≤ (a : ℕ) * (lowerCD w).2 := Nat.le_mul_of_pos_left _ a.pos
        have := ih.1
        have := ih.2
        omega

private theorem matrix_bottom (w : List ℕ+) :
    (lowerInitialWordMatrix w).c = ((lowerCD w).1:ℝ) ∧
    (lowerInitialWordMatrix w).d = ((lowerCD w).2:ℝ) := by
  induction w using List.reverseRecOn with
  | nil =>
      rw [wm_eq, cd_eq]
      constructor <;> norm_num
  | append_singleton w a ih =>
      rw [wm_append, cd_append]
      obtain ⟨h1, h2⟩ := ih
      simp only [lowerInitialMatMul, Nat.cast_add, Nat.cast_mul]
      constructor
      · show (lowerInitialWordMatrix w).c * 0 + (lowerInitialWordMatrix w).d * 1 = _
        rw [h2]; ring
      · show (lowerInitialWordMatrix w).c * 1 + (lowerInitialWordMatrix w).d * ((a : ℕ) : ℝ) = _
        rw [h1, h2]; ring

private theorem pe_pos : ∀ (w : List ℕ+) (t : ℝ), 0 < t → 0 < prefixEval w t
  | [], t, ht => by simpa [prefixEval] using ht
  | a :: w, t, ht => by
      rw [prefixEval]
      have h := pe_pos w t ht
      have ha : (0:ℝ) < ((a : ℕ):ℝ) := by exact_mod_cast a.pos
      positivity
private theorem tau_pos : 0 < lowerTau := by
  have h := Real.sqrt_nonneg 3
  have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  unfold lowerTau
  nlinarith
private theorem theta3_pos : 0 < lowerTheta 3 := pe_pos _ _ tau_pos
private theorem theta25_pos : 0 < lowerTheta 25 := pe_pos _ _ tau_pos
private theorem theta36_pos : 0 < lowerTheta 36 := by change 0 < lowerTau/2; exact div_pos tau_pos (by norm_num)
private theorem theta63_pos : 0 < lowerTheta 63 := pe_pos _ _ tau_pos
private theorem theta66_pos : 0 < lowerTheta 66 := pe_pos _ _ tau_pos

private theorem den_ratio (w : List ℕ+) (t : ℝ) :
    1+lowerRatio w*t = lowerInitialMatDen (lowerInitialWordMatrix w) t / ((lowerCD w).2:ℝ) := by
  have hd : ((lowerCD w).2:ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (cd_pos w))
  unfold lowerRatio lowerInitialMatDen
  rw [(matrix_bottom w).1, (matrix_bottom w).2]
  field_simp
  ring

private theorem threshold_formula (u v : List ℕ+) (h : lowerNormalize (u,v) = (u,v))
    (c : ℝ) (i j k l : ℕ) :
    lowerThreshold (u,v) c i j k l =
      lowerScale (u,v) * (c*lowerInitialMatDen (lowerInitialWordMatrix v) (lowerTheta j)*
        lowerInitialMatDen (lowerInitialWordMatrix v) (lowerTheta l)) /
      (lowerInitialMatDen (lowerInitialWordMatrix u) (lowerTheta i)*
        lowerInitialMatDen (lowerInitialWordMatrix u) (lowerTheta k)) := by
  unfold lowerThreshold
  rw [h]
  dsimp only
  rw [den_ratio, den_ratio, den_ratio, den_ratio]
  unfold lowerScale
  dsimp only
  ring_nf
  simp only [inv_inv]
  ring

private theorem scale_pos (u v : List ℕ+) : 0 < lowerScale (u,v) := by
  have hu : 0 < ((lowerCD u).2:ℝ) := by exact_mod_cast cd_pos u
  have hv : 0 < ((lowerCD v).2:ℝ) := by exact_mod_cast cd_pos v
  unfold lowerScale
  positivity

private theorem threshold_lt_scale (hf : FractionProperty) (u v : List ℕ+)
    (h : lowerNormalize (u,v) = (u,v)) (c : ℝ) (i j k l : ℕ)
    (hi : 0 < lowerTheta i) (hk : 0 < lowerTheta k)
    (hm : c*lowerInitialMatDen (lowerInitialWordMatrix v) (lowerTheta j)*
      lowerInitialMatDen (lowerInitialWordMatrix v) (lowerTheta l) <
      lowerInitialMatDen (lowerInitialWordMatrix u) (lowerTheta i)*
      lowerInitialMatDen (lowerInitialWordMatrix u) (lowerTheta k)) :
    lowerThreshold (u,v) c i j k l < lowerScale (u,v) := by
  rw [threshold_formula u v h]
  apply (div_lt_iff₀ (mul_pos (hf u _ hi).2.1 (hf u _ hk).2.1)).2
  exact mul_lt_mul_of_pos_left hm (scale_pos u v)

private theorem survivor_words (c : LowerBridgeCase) (r : LowerBridgeRecord)
    (hr : r ∈ lowerBridgeRecords c) (hk : r.kind = .h7 ∨ r.kind = .notA9) :
    r.words = ([1],[1]) := by
  have hb : (lowerBridgeRecords c).all (fun r => decide
      ((r.kind = .h7 ∨ r.kind = .notA9) → r.words = ([1],[1]))) = true := by
    cases c <;> decide
  have hh : ∀ r ∈ lowerBridgeRecords c,
      (r.kind = .h7 ∨ r.kind = .notA9) → r.words = ([1],[1]) := by
    simpa only [List.all_eq_true, decide_eq_true_eq] using hb
  exact hh r hr hk

private theorem survivor_wide (c : LowerBridgeCase) (n k : ℕ)
    (hw : ∀ r ∈ lowerBridgeRecords c, r.kind = .width → lowerBridgeRecordFact c n k r) :
    lowerWidth ((lowerBridgePair c n k).2++[1]) < lowerWidth ((lowerBridgePair c n k).1++[1]) := by
  let r := (lowerBridgeRecords c)[0]'(by cases c <;> decide)
  have hr : r ∈ lowerBridgeRecords c := List.getElem_mem _
  have hk : r.kind = .width := by cases c <;> rfl
  have hh := hw r hr hk
  cases c <;> exact hh

private theorem den_scale (s : ℝ) (a : LowerInitialMatrix) (t : ℝ) :
    lowerInitialMatDen (lowerInitialMatScale s a) t = s * lowerInitialMatDen a t := by
  unfold lowerInitialMatDen lowerInitialMatScale
  ring
end OtherBridge

theorem solution (hfrac : ∀ (w : List ℕ+) (t : ℝ), 0 < t → prefixEval w t = lowerInitialMatEval (lowerInitialWordMatrix w) t ∧ 0 < lowerInitialMatDen (lowerInitialWordMatrix w) t ∧ (lowerInitialWordMatrix w).a*(lowerInitialWordMatrix w).d - (lowerInitialWordMatrix w).b*(lowerInitialWordMatrix w).c = (-1:ℝ)^w.length) (c : LowerBridgeCase) (n k : ℕ) (hc : lowerBridgeZero c = decide (n=0)) (hm : lowerInitialSeamLink (lowerBridgeSeamCase c) n (lowerBridgeK c k) 0) (hn : lowerBridgeNumeric c (lowerInitialX n) (lowerInitialY k)) (hw : ∀ r ∈ lowerBridgeRecords c, r.kind = .width → lowerBridgeRecordFact c n k r) (r : LowerBridgeRecord) (hr : r ∈ lowerBridgeRecords c) (hk : r.kind = .h7 ∨ r.kind = .notA9) : lowerBridgeRecordFact c n k r := by
  have hwds := survivor_words c r hr hk
  have hwid := survivor_wide c n k hw
  have hnorm : lowerNormalize (lowerBridgeAppend (lowerBridgePair c n k) r.words) =
      lowerBridgeAppend (lowerBridgePair c n k) r.words := by
    simp only [hwds, lowerBridgeAppend, lowerNormalize]
    rw [if_pos (le_of_lt hwid)]
  dsimp only [lowerBridgeAppend] at hnorm
  obtain ⟨s, hs, h1, h2⟩ := bridge_link c n k hm
  have h1a := congrArg (fun m => lowerInitialMatMul m (lowerInitialWordMatrix r.words.1)) h1
  have h2a := congrArg (fun m => lowerInitialMatMul m (lowerInitialWordMatrix r.words.2)) h2
  rw [← wm_append_all, scale_mul] at h1a h2a
  have hnum := hn r hr
  rcases hk with hk | hk
  · simp only [lowerBridgeNumerator, hk, lowerBridgeMatAppend] at hnum
    have hb : (31/100:ℝ)*lowerInitialMatDen (lowerInitialWordMatrix
        ((lowerBridgePair c n k).2++r.words.2)) (lowerTheta 63)*
        lowerInitialMatDen (lowerInitialWordMatrix ((lowerBridgePair c n k).2++r.words.2)) (lowerTheta 66) <
      lowerInitialMatDen (lowerInitialWordMatrix ((lowerBridgePair c n k).1++r.words.1)) (lowerTheta 3)*
        lowerInitialMatDen (lowerInitialWordMatrix ((lowerBridgePair c n k).1++r.words.1)) (lowerTheta 25) := by
      rw [h1a, h2a, den_scale, den_scale, den_scale, den_scale]
      nlinarith [mul_pos (sq_pos_of_pos hs) hnum]
    simpa only [lowerBridgeRecordFact, hk, lowerBridgeAppend, hnorm] using
      (threshold_lt_scale hfrac _ _ hnorm (31/100) 3 63 25 66 theta3_pos theta25_pos hb).le
  · simp only [lowerBridgeNumerator, hk, lowerBridgeMatAppend] at hnum
    have hb : ((3-Real.sqrt 3)/2)*lowerInitialMatDen (lowerInitialWordMatrix
        ((lowerBridgePair c n k).2++r.words.2)) (lowerTheta 63)*
        lowerInitialMatDen (lowerInitialWordMatrix ((lowerBridgePair c n k).2++r.words.2)) (lowerTheta 66) <
      lowerInitialMatDen (lowerInitialWordMatrix ((lowerBridgePair c n k).1++r.words.1)) (lowerTheta 36)*
        lowerInitialMatDen (lowerInitialWordMatrix ((lowerBridgePair c n k).1++r.words.1)) (lowerTheta 63) := by
      rw [h1a, h2a, den_scale, den_scale, den_scale, den_scale]
      nlinarith [mul_pos (sq_pos_of_pos hs) hnum]
    have hh := threshold_lt_scale hfrac _ _ hnorm ((3-Real.sqrt 3)/2) 36 63 63 66 theta36_pos theta63_pos hb
    simpa only [lowerBridgeRecordFact, hk, lowerA, hnorm, lowerBridgeAppend, not_le] using hh
#print axioms solution

example : (∀ (hfrac : ∀ (w : List ℕ+) (t : ℝ), 0 < t → prefixEval w t = lowerInitialMatEval (lowerInitialWordMatrix w) t ∧ 0 < lowerInitialMatDen (lowerInitialWordMatrix w) t ∧ (lowerInitialWordMatrix w).a*(lowerInitialWordMatrix w).d - (lowerInitialWordMatrix w).b*(lowerInitialWordMatrix w).c = (-1:ℝ)^w.length) (c : LowerBridgeCase) (n k : ℕ) (hc : lowerBridgeZero c = decide (n=0)) (hm : lowerInitialSeamLink (lowerBridgeSeamCase c) n (lowerBridgeK c k) 0) (hn : lowerBridgeNumeric c (lowerInitialX n) (lowerInitialY k)) (hw : ∀ r ∈ lowerBridgeRecords c, r.kind = .width → lowerBridgeRecordFact c n k r) (r : LowerBridgeRecord) (hr : r ∈ lowerBridgeRecords c) (hk : r.kind = .h7 ∨ r.kind = .notA9) ,  lowerBridgeRecordFact c n k r) := @solution
