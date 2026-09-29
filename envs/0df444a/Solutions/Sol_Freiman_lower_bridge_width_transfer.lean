-- Prove2me | solution 1 for Freiman.lower_bridge_width_transfer
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T10:14:07.133881+00:00
-- url     : https://prove2.me/submissions/d65cec20-037b-44df-9bd9-7d7c7a7884f3

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

theorem solution (hfrac : ∀ (w : List ℕ+) (t : ℝ), 0 < t → prefixEval w t = lowerInitialMatEval (lowerInitialWordMatrix w) t ∧ 0 < lowerInitialMatDen (lowerInitialWordMatrix w) t ∧ (lowerInitialWordMatrix w).a*(lowerInitialWordMatrix w).d - (lowerInitialWordMatrix w).b*(lowerInitialWordMatrix w).c = (-1:ℝ)^w.length) (c : LowerBridgeCase) (n k : ℕ) (hc : lowerBridgeZero c = decide (n=0)) (hm : lowerInitialSeamLink (lowerBridgeSeamCase c) n (lowerBridgeK c k) 0) (hn : lowerBridgeNumeric c (lowerInitialX n) (lowerInitialY k)) (r : LowerBridgeRecord) (hr : r ∈ lowerBridgeRecords c) (hk : r.kind = .width) : lowerBridgeRecordFact c n k r := by
  obtain ⟨s, hs, h1, h2⟩ := bridge_link c n k hm
  have h1a := congrArg (fun m => lowerInitialMatMul m (lowerInitialWordMatrix r.words.1)) h1
  have h2a := congrArg (fun m => lowerInitialMatMul m (lowerInitialWordMatrix r.words.2)) h2
  rw [← wm_append_all, scale_mul] at h1a h2a
  have hnum := hn r hr
  cases hwide : r.wider
  · simp only [lowerBridgeNumerator, hk, lowerBridgeMatAppend, hwide, Bool.false_eq_true,
      ite_false] at hnum
    simpa only [lowerBridgeRecordFact, hk, lowerBridgeAppend, hwide,
      Bool.false_eq_true, ite_false] using
      width_reverse hfrac _ _ s hs _ _ h1a h2a (sub_pos.mp hnum)
  · simp only [lowerBridgeNumerator, hk, lowerBridgeMatAppend, hwide, ite_true] at hnum
    simpa only [lowerBridgeRecordFact, hk, lowerBridgeAppend, hwide, ite_true] using
      width_reverse hfrac _ _ s hs _ _ h2a h1a (sub_pos.mp hnum)
#print axioms solution

example : (∀ (hfrac : ∀ (w : List ℕ+) (t : ℝ), 0 < t → prefixEval w t = lowerInitialMatEval (lowerInitialWordMatrix w) t ∧ 0 < lowerInitialMatDen (lowerInitialWordMatrix w) t ∧ (lowerInitialWordMatrix w).a*(lowerInitialWordMatrix w).d - (lowerInitialWordMatrix w).b*(lowerInitialWordMatrix w).c = (-1:ℝ)^w.length) (c : LowerBridgeCase) (n k : ℕ) (hc : lowerBridgeZero c = decide (n=0)) (hm : lowerInitialSeamLink (lowerBridgeSeamCase c) n (lowerBridgeK c k) 0) (hn : lowerBridgeNumeric c (lowerInitialX n) (lowerInitialY k)) (r : LowerBridgeRecord) (hr : r ∈ lowerBridgeRecords c) (hk : r.kind = .width) ,  lowerBridgeRecordFact c n k r) := @solution
