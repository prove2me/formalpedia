-- Prove2me | solution 1 for Freiman.lower_bridge_contact_transfer
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T10:20:09.815854+00:00
-- url     : https://prove2.me/submissions/0a816639-2b2d-4e8e-8594-7edeb80688be

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

namespace OtherBridgePeriodPositive

open Freiman

theorem u_step : ∀ n : ℕ, 0 ≤ lowerInitialU n ∧ lowerInitialU n < lowerInitialU (n+1) := by
  intro n
  induction n with
  | zero => constructor <;> decide
  | succ m ih =>
      obtain ⟨h0, h1⟩ := ih
      have hpos : 0 < lowerInitialU (m+1) := lt_of_le_of_lt h0 h1
      refine ⟨hpos.le, ?_⟩
      have he : lowerInitialU (m+2) = 86 * lowerInitialU (m+1) - lowerInitialU m := rfl
      rw [he]
      nlinarith

theorem result (n : ℕ) (hn : 0 < n) : 0 < lowerInitialU n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact lt_of_le_of_lt (u_step m).1 (u_step m).2

end OtherBridgePeriodPositive

namespace OtherBridgePeriodRecurrence

open Freiman

theorem wm_eq (w : List ℕ+) : lowerInitialWordMatrix w =
    List.foldl (fun m (d : ℕ) => lowerInitialMatMul m ⟨0,1,1,(d : ℝ)⟩)
      ⟨1,0,0,1⟩ (w.map PNat.val) := by
  have hbind : (do let a ← w; pure (a : ℕ)) = w.map PNat.val := by
    induction w with
    | nil => rfl
    | cons a w ih => simpa using ih
  unfold lowerInitialWordMatrix
  rw [hbind]

theorem mm_assoc (x y z : LowerInitialMatrix) :
    lowerInitialMatMul (lowerInitialMatMul x y) z
      = lowerInitialMatMul x (lowerInitialMatMul y z) := by
  obtain ⟨a,b,c,d⟩ := x
  obtain ⟨e,f,g,h⟩ := y
  obtain ⟨i,j,k,l⟩ := z
  simp only [lowerInitialMatMul, LowerInitialMatrix.mk.injEq]
  refine ⟨by ring, by ring, by ring, by ring⟩

theorem mm_one_left (x : LowerInitialMatrix) :
    lowerInitialMatMul ⟨1,0,0,1⟩ x = x := by
  obtain ⟨a,b,c,d⟩ := x
  simp only [lowerInitialMatMul, LowerInitialMatrix.mk.injEq]
  refine ⟨by ring, by ring, by ring, by ring⟩

theorem wm_gen : ∀ (v : List ℕ+) (X : LowerInitialMatrix),
    List.foldl (fun m (d : ℕ) => lowerInitialMatMul m ⟨0,1,1,(d : ℝ)⟩) X (v.map PNat.val)
      = lowerInitialMatMul X (lowerInitialWordMatrix v) := by
  intro v
  induction v with
  | nil =>
      intro X
      obtain ⟨a,b,c,d⟩ := X
      simp only [List.map_nil, List.foldl_nil, wm_eq, lowerInitialMatMul,
        LowerInitialMatrix.mk.injEq]
      refine ⟨by ring, by ring, by ring, by ring⟩
  | cons a v ih =>
      intro X
      have h1 : lowerInitialWordMatrix (a :: v)
          = lowerInitialMatMul ⟨0,1,1,((a : ℕ) : ℝ)⟩ (lowerInitialWordMatrix v) := by
        rw [wm_eq (a :: v)]
        simp only [List.map_cons, List.foldl_cons]
        rw [mm_one_left, ih ⟨0,1,1,((a : ℕ) : ℝ)⟩]
      simp only [List.map_cons, List.foldl_cons]
      rw [ih (lowerInitialMatMul X ⟨0,1,1,((a : ℕ) : ℝ)⟩), h1, mm_assoc]

theorem wm_mul (u v : List ℕ+) :
    lowerInitialWordMatrix (u ++ v)
      = lowerInitialMatMul (lowerInitialWordMatrix u) (lowerInitialWordMatrix v) := by
  rw [wm_eq (u ++ v), List.map_append, List.foldl_append, ← wm_eq u, wm_gen]

theorem repeat_succ (n : ℕ) :
    lowerRepeat lowerPeriod (n+1) = lowerPeriod ++ lowerRepeat lowerPeriod n := by
  unfold lowerRepeat
  rw [List.replicate_succ]
  simp

theorem period_matrix : lowerInitialWordMatrix lowerPeriod = ⟨14,19,53,72⟩ := by
  rw [wm_eq]
  norm_num [lowerPeriod, lowerInitialMatMul]

theorem prm : ∀ m : ℕ, lowerInitialWordMatrix (lowerRepeat lowerPeriod (m+1)) =
    ⟨14*(lowerInitialU (m+1):ℝ)-(lowerInitialU m:ℝ), 19*(lowerInitialU (m+1):ℝ),
     53*(lowerInitialU (m+1):ℝ), 72*(lowerInitialU (m+1):ℝ)-(lowerInitialU m:ℝ)⟩ := by
  intro m
  induction m with
  | zero =>
      rw [repeat_succ]
      show lowerInitialWordMatrix (lowerPeriod ++ lowerRepeat lowerPeriod 0) = _
      rw [show lowerRepeat lowerPeriod 0 = ([] : List ℕ+) from rfl, List.append_nil,
        period_matrix]
      norm_num [show lowerInitialU 0 = 0 from rfl, show lowerInitialU 1 = 1 from rfl]
  | succ n ih =>
      rw [repeat_succ, wm_mul, period_matrix, ih]
      have he : ((lowerInitialU (n+1+1) : ℤ) : ℝ)
          = 86 * ((lowerInitialU (n+1) : ℤ) : ℝ) - ((lowerInitialU n : ℤ) : ℝ) := by
        rw [show lowerInitialU (n+1+1) = 86 * lowerInitialU (n+1) - lowerInitialU n from rfl]
        push_cast
        ring
      simp only [lowerInitialMatMul, LowerInitialMatrix.mk.injEq, he]
      refine ⟨by ring, by ring, by ring, by ring⟩

theorem result (n : ℕ) (hn : 0 < n) :
    lowerInitialWordMatrix (lowerRepeat lowerPeriod n) =
    ⟨14*(lowerInitialU n:ℝ)-(lowerInitialU (n-1):ℝ),19*(lowerInitialU n:ℝ),
      53*(lowerInitialU n:ℝ),72*(lowerInitialU n:ℝ)-(lowerInitialU (n-1):ℝ)⟩ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simpa using prm m

end OtherBridgePeriodRecurrence

namespace OtherBridgePeriodScaled

open Freiman

theorem result (n : ℕ) (hn : 0 < n) (hp : 0 < lowerInitialU n)
    (hm : lowerInitialWordMatrix (lowerRepeat lowerPeriod n) =
    ⟨14*(lowerInitialU n:ℝ)-(lowerInitialU (n-1):ℝ),19*(lowerInitialU n:ℝ),
      53*(lowerInitialU n:ℝ),72*(lowerInitialU n:ℝ)-(lowerInitialU (n-1):ℝ)⟩) :
    lowerInitialWordMatrix (lowerRepeat lowerPeriod n) =
    lowerInitialMatScale (lowerInitialU n:ℝ) (lowerInitialP false (lowerInitialX n)) := by
  have hU : ((lowerInitialU n : ℤ) : ℝ) ≠ 0 := by
    have h : (0:ℝ) < ((lowerInitialU n : ℤ) : ℝ) := by exact_mod_cast hp
    linarith
  have hP : lowerInitialP false (lowerInitialX n)
      = ⟨14 - lowerInitialX n, 19, 53, 72 - lowerInitialX n⟩ := by
    simp [lowerInitialP]
  rw [hm, hP]
  simp only [lowerInitialMatScale, lowerInitialX, LowerInitialMatrix.mk.injEq]
  refine ⟨?_, by ring, by ring, ?_⟩ <;> field_simp <;> ring

end OtherBridgePeriodScaled

namespace OtherBridgeRunMatrix

open Freiman

theorem wm_eq (w : List ℕ+) : lowerInitialWordMatrix w =
    List.foldl (fun m (d : ℕ) => lowerInitialMatMul m ⟨0,1,1,(d : ℝ)⟩)
      ⟨1,0,0,1⟩ (w.map PNat.val) := by
  have hbind : (do let a ← w; pure (a : ℕ)) = w.map PNat.val := by
    induction w with
    | nil => rfl
    | cons a w ih => simpa using ih
  unfold lowerInitialWordMatrix
  rw [hbind]

theorem mm_assoc (x y z : LowerInitialMatrix) :
    lowerInitialMatMul (lowerInitialMatMul x y) z
      = lowerInitialMatMul x (lowerInitialMatMul y z) := by
  obtain ⟨a,b,c,d⟩ := x
  obtain ⟨e,f,g,h⟩ := y
  obtain ⟨i,j,k,l⟩ := z
  simp only [lowerInitialMatMul, LowerInitialMatrix.mk.injEq]
  refine ⟨by ring, by ring, by ring, by ring⟩

theorem mm_one_left (x : LowerInitialMatrix) :
    lowerInitialMatMul ⟨1,0,0,1⟩ x = x := by
  obtain ⟨a,b,c,d⟩ := x
  simp only [lowerInitialMatMul, LowerInitialMatrix.mk.injEq]
  refine ⟨by ring, by ring, by ring, by ring⟩

theorem wm_gen : ∀ (v : List ℕ+) (X : LowerInitialMatrix),
    List.foldl (fun m (d : ℕ) => lowerInitialMatMul m ⟨0,1,1,(d : ℝ)⟩) X (v.map PNat.val)
      = lowerInitialMatMul X (lowerInitialWordMatrix v) := by
  intro v
  induction v with
  | nil =>
      intro X
      obtain ⟨a,b,c,d⟩ := X
      simp only [List.map_nil, List.foldl_nil, wm_eq, lowerInitialMatMul,
        LowerInitialMatrix.mk.injEq]
      refine ⟨by ring, by ring, by ring, by ring⟩
  | cons a v ih =>
      intro X
      have h1 : lowerInitialWordMatrix (a :: v)
          = lowerInitialMatMul ⟨0,1,1,((a : ℕ) : ℝ)⟩ (lowerInitialWordMatrix v) := by
        rw [wm_eq (a :: v)]
        simp only [List.map_cons, List.foldl_cons]
        rw [mm_one_left, ih ⟨0,1,1,((a : ℕ) : ℝ)⟩]
      simp only [List.map_cons, List.foldl_cons]
      rw [ih (lowerInitialMatMul X ⟨0,1,1,((a : ℕ) : ℝ)⟩), h1, mm_assoc]

theorem wm_mul (u v : List ℕ+) :
    lowerInitialWordMatrix (u ++ v)
      = lowerInitialMatMul (lowerInitialWordMatrix u) (lowerInitialWordMatrix v) := by
  rw [wm_eq (u ++ v), List.map_append, List.foldl_append, ← wm_eq u, wm_gen]

theorem repeat_succ (n : ℕ) :
    lowerRepeat lowerPeriod (n+1) = lowerPeriod ++ lowerRepeat lowerPeriod n := by
  unfold lowerRepeat
  rw [List.replicate_succ]
  simp

theorem v_pos : ∀ k : ℕ, 0 < lowerInitialV (k+1) := by
  intro k
  induction k with
  | zero => decide
  | succ m ih =>
      show 0 < lowerInitialV (m+2)
      have he : lowerInitialV (m+2) = 3 * lowerInitialV (m+1) + lowerInitialV m := rfl
      omega

theorem v_rec (k : ℕ) : ((lowerInitialV (k+2) : ℕ) : ℝ)
    = 3 * ((lowerInitialV (k+1) : ℕ) : ℝ) + ((lowerInitialV k : ℕ) : ℝ) := by
  rw [show lowerInitialV (k+2) = 3 * lowerInitialV (k+1) + lowerInitialV k from rfl]
  push_cast
  ring

theorem three_matrix : lowerInitialWordMatrix [(3 : ℕ+)] = ⟨0,1,1,3⟩ := by
  rw [wm_eq]
  norm_num [lowerInitialMatMul]

theorem rep_matrix : ∀ k : ℕ, lowerInitialWordMatrix (List.replicate k (3 : ℕ+))
    = ⟨((lowerInitialV (k+1) : ℕ) : ℝ) - 3*((lowerInitialV k : ℕ) : ℝ),
       ((lowerInitialV k : ℕ) : ℝ), ((lowerInitialV k : ℕ) : ℝ),
       ((lowerInitialV (k+1) : ℕ) : ℝ)⟩ := by
  intro k
  induction k with
  | zero =>
      rw [show List.replicate 0 (3 : ℕ+) = ([] : List ℕ+) from rfl, wm_eq]
      norm_num [show lowerInitialV 0 = 0 from rfl, show lowerInitialV 1 = 1 from rfl]
  | succ m ih =>
      rw [List.replicate_succ', wm_mul, ih, three_matrix]
      simp only [lowerInitialMatMul, LowerInitialMatrix.mk.injEq]
      have h := v_rec m
      refine ⟨by push_cast; linarith, by push_cast; ring, by push_cast; linarith,
        by push_cast; linarith⟩

theorem result (k : ℕ) :
    lowerInitialWordMatrix (List.replicate (k+1) (3:ℕ+)) =
      lowerInitialMatScale (lowerInitialV (k+1):ℝ) (lowerInitialK (lowerInitialY k)) ∧
    lowerInitialWordMatrix (List.replicate k (3:ℕ+)) =
      lowerInitialMatScale (lowerInitialV (k+1):ℝ) (lowerInitialKPrev (lowerInitialY k)) := by
  have hp : ((lowerInitialV (k+1) : ℕ) : ℝ) ≠ 0 := by
    have h : (0:ℝ) < ((lowerInitialV (k+1) : ℕ) : ℝ) := by exact_mod_cast v_pos k
    linarith
  have h := v_rec k
  constructor
  · rw [rep_matrix (k+1)]
    simp only [lowerInitialMatScale, lowerInitialK, lowerInitialY, LowerInitialMatrix.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> field_simp <;> linarith
  · rw [rep_matrix k]
    simp only [lowerInitialMatScale, lowerInitialKPrev, lowerInitialY, LowerInitialMatrix.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> field_simp <;> ring

end OtherBridgeRunMatrix

namespace OtherBridge
private theorem period_matrix (n : ℕ) (hn : 0 < n) : lowerInitialWordMatrix (lowerRepeat lowerPeriod n) =
    lowerInitialMatScale (lowerInitialU n:ℝ) (lowerInitialP false (lowerInitialX n)) :=
  OtherBridgePeriodScaled.result n hn (OtherBridgePeriodPositive.result n hn)
    (OtherBridgePeriodRecurrence.result n hn)

private theorem mul_scale (s : ℝ) (a b : LowerInitialMatrix) :
    lowerInitialMatMul a (lowerInitialMatScale s b) = lowerInitialMatScale s (lowerInitialMatMul a b) := by
  cases a; cases b
  unfold lowerInitialMatScale lowerInitialMatMul
  congr 1 <;> ring

private theorem scale_scale (s t : ℝ) (a : LowerInitialMatrix) :
    lowerInitialMatScale s (lowerInitialMatScale t a) = lowerInitialMatScale (s*t) a := by
  cases a
  unfold lowerInitialMatScale
  congr 1 <;> ring

private theorem common_link (c : LowerBridgeCase) (n k : ℕ)
    (hc : lowerBridgeZero c = decide (n=0)) (hf : lowerBridgeFamily c = .C) :
    ∃ s : ℝ, 0 < s ∧
      lowerInitialWordMatrix (lowerBridgeCommonPair c n k).1 =
        lowerInitialMatScale s (lowerBridgeCommonMatrices c (lowerInitialX n) (lowerInitialY k)).1 ∧
      lowerInitialWordMatrix (lowerBridgeCommonPair c n k).2 =
        lowerInitialMatScale s (lowerBridgeCommonMatrices c (lowerInitialX n) (lowerInitialY k)).2 := by
  have hp : ∃ sp : ℝ, 0 < sp ∧ lowerInitialWordMatrix (lowerRepeat lowerPeriod n) =
      lowerInitialMatScale sp (lowerInitialP (lowerBridgeZero c) (lowerInitialX n)) := by
    by_cases hn : n = 0
    · subst n
      refine ⟨1, by norm_num, ?_⟩
      have hz : lowerBridgeZero c = true := by simpa using hc
      simp [hz, lowerRepeat, lowerInitialP, wm_eq, lowerInitialMatScale]
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hz : lowerBridgeZero c = false := by simpa [hn] using hc
      refine ⟨(lowerInitialU n:ℝ), ?_, ?_⟩
      · exact_mod_cast OtherBridgePeriodPositive.result n hnpos
      · rw [hz]; exact period_matrix n hnpos
  obtain ⟨sp, hsp, hp⟩ := hp
  have hsv : 0 < ((lowerInitialV (k+1):ℕ):ℝ) := by exact_mod_cast OtherBridgeRunMatrix.v_pos k
  have hr := (OtherBridgeRunMatrix.result k).1
  refine ⟨sp*(lowerInitialV (k+1):ℝ), mul_pos hsp hsv, ?_, ?_⟩ <;>
    simp only [lowerBridgeCommonPair, hf, ite_true, lowerBridgeCommonMatrices] <;>
    rw [wm_append_all, wm_append_all, wm_append_all, hp, hr] <;>
    simp only [mul_scale, scale_mul, scale_scale, mul_comm]

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
private theorem den_scale (s : ℝ) (a : LowerInitialMatrix) (t : ℝ) :
    lowerInitialMatDen (lowerInitialMatScale s a) t = s * lowerInitialMatDen a t := by
  unfold lowerInitialMatDen lowerInitialMatScale
  ring
private theorem pow_par (m n : ℕ) (h : m % 2 = n % 2) : (-1:ℝ)^m = (-1:ℝ)^n := by
  rcases Nat.even_or_odd m with he | ho
  · have hn : Even n := by rw [Nat.even_iff] at he ⊢; omega
    rw [he.neg_one_pow, hn.neg_one_pow]
  · have hn : Odd n := by rw [Nat.odd_iff] at ho ⊢; omega
    rw [ho.neg_one_pow, hn.neg_one_pow]
private theorem sq_pow_one (n : ℕ) : (-1:ℝ)^n * (-1:ℝ)^n = 1 := by
  rw [← pow_add]
  have h : Even (n+n) := ⟨n, by omega⟩
  exact h.neg_one_pow

private theorem difference_sign (hf : FractionProperty) (w : List ℕ+) (x y : ℝ)
    (hx : 0 < x) (hy : 0 < y) :
    (prefixEval w y-prefixEval w x) *
      (lowerInitialMatDen (lowerInitialWordMatrix w) x * lowerInitialMatDen (lowerInitialWordMatrix w) y) =
      (y-x)*(-1:ℝ)^w.length := by
  obtain ⟨e1, dd1, det⟩ := hf w x hx
  obtain ⟨e2, dd2, _⟩ := hf w y hy
  rw [e1, e2]
  unfold lowerInitialMatEval lowerInitialMatDen at *
  rw [cross_diff _ _ _ _ (ne_of_gt dd1) (ne_of_gt dd2)]
  linear_combination (y-x)*det

private theorem contact_generic (hf : FractionProperty) (p u v : LowerPair)
    (m : LowerInitialMatrix × LowerInitialMatrix) (s : ℝ) (hs : 0 < s)
    (hm1 : lowerInitialWordMatrix p.1 = lowerInitialMatScale s m.1)
    (hm2 : lowerInitialWordMatrix p.2 = lowerInitialMatScale s m.2) (opposite : Bool)
    (hpar : (-1:ℝ)^p.2.length = (if opposite then -1 else 1)*(-1:ℝ)^p.1.length)
    (hn : 0 < lowerBridgeDifference m u v opposite) :
    0 < (-1:ℝ)^p.1.length *
      (prefixEval (p.1++u.1) lowerTau + prefixEval (p.2++u.2) lowerTau -
       prefixEval (p.1++v.1) lowerTau - prefixEval (p.2++v.2) lowerTau) := by
  let a := prefixEval u.1 lowerTau
  let b := prefixEval v.1 lowerTau
  let cc := prefixEval u.2 lowerTau
  let d := prefixEval v.2 lowerTau
  have ha : 0 < a := pe_pos _ _ tau_pos
  have hb : 0 < b := pe_pos _ _ tau_pos
  have hcc : 0 < cc := pe_pos _ _ tau_pos
  have hd : 0 < d := pe_pos _ _ tau_pos
  let d1a := lowerInitialMatDen (lowerInitialWordMatrix p.1) a
  let d1b := lowerInitialMatDen (lowerInitialWordMatrix p.1) b
  let d2c := lowerInitialMatDen (lowerInitialWordMatrix p.2) cc
  let d2d := lowerInitialMatDen (lowerInitialWordMatrix p.2) d
  have hp : 0 < (d1b*d1a)*(d2d*d2c) :=
    mul_pos (mul_pos (hf p.1 _ hb).2.1 (hf p.1 _ ha).2.1)
      (mul_pos (hf p.2 _ hd).2.1 (hf p.2 _ hcc).2.1)
  have hn' : 0 < (a-b)*d2c*d2d + (if opposite then -(cc-d) else cc-d)*d1a*d1b := by
    have hh := mul_pos (sq_pos_of_pos hs) hn
    dsimp only [d1a, d1b, d2c, d2d]
    rw [hm1, hm2, den_scale, den_scale, den_scale, den_scale]
    unfold lowerBridgeDifference at hh
    cases opposite <;> simp only [Bool.false_eq_true, ite_false, ite_true] at * <;> nlinarith
  have e1 := difference_sign hf p.1 b a hb ha
  have e2 := difference_sign hf p.2 d cc hd hcc
  have heq : ((-1:ℝ)^p.1.length *
      (prefixEval p.1 a-prefixEval p.1 b+prefixEval p.2 cc-prefixEval p.2 d)) *
      ((d1b*d1a)*(d2d*d2c)) =
      (a-b)*d2c*d2d + (if opposite then -(cc-d) else cc-d)*d1a*d1b := by
    have hstep : ((-1:ℝ)^p.1.length *
        (prefixEval p.1 a-prefixEval p.1 b+prefixEval p.2 cc-prefixEval p.2 d)) *
        ((d1b*d1a)*(d2d*d2c)) =
        (-1:ℝ)^p.1.length * ((prefixEval p.1 a-prefixEval p.1 b)*(d1b*d1a))*(d2d*d2c) +
        (-1:ℝ)^p.1.length * ((prefixEval p.2 cc-prefixEval p.2 d)*(d2d*d2c))*(d1b*d1a) := by ring
    rw [hstep, e1, e2, hpar]
    have hh := sq_pow_one p.1.length
    cases opposite
    · simp only [Bool.false_eq_true, ite_false]
      linear_combination ((a-b)*(d2c*d2d) + (cc-d)*(d1a*d1b))*hh
    · simp only [ite_true]
      linear_combination ((a-b)*(d2c*d2d) - (cc-d)*(d1a*d1b))*hh
  rw [pe_append, pe_append, pe_append, pe_append]
  have hresult : 0 < (-1:ℝ)^p.1.length *
      (prefixEval p.1 a-prefixEval p.1 b+prefixEval p.2 cc-prefixEval p.2 d) := by
    nlinarith [heq]
  convert hresult using 1 <;> dsimp only [a, b, cc, d] <;> ring

end OtherBridge

theorem solution (hfrac : ∀ (w : List ℕ+) (t : ℝ), 0 < t → prefixEval w t = lowerInitialMatEval (lowerInitialWordMatrix w) t ∧ 0 < lowerInitialMatDen (lowerInitialWordMatrix w) t ∧ (lowerInitialWordMatrix w).a*(lowerInitialWordMatrix w).d - (lowerInitialWordMatrix w).b*(lowerInitialWordMatrix w).c = (-1:ℝ)^w.length) (c : LowerBridgeCase) (n k : ℕ) (hc : lowerBridgeZero c = decide (n=0)) (hm : lowerInitialSeamLink (lowerBridgeSeamCase c) n (lowerBridgeK c k) 0) (hn : lowerBridgeNumeric c (lowerInitialX n) (lowerInitialY k)) (r : LowerBridgeRecord) (hr : r ∈ lowerBridgeRecords c) (hk : r.kind ≠ .width ∧ r.kind ≠ .auxiliary ∧ r.kind ≠ .h7 ∧ r.kind ≠ .notA9) : lowerBridgeRecordFact c n k r := by
  have hfamily : (r.kind = .cLower ∨ r.kind = .cUpper) → lowerBridgeFamily c = .C := by
    have hb : (lowerBridgeRecords c).all (fun r => decide
        ((r.kind = .cLower ∨ r.kind = .cUpper) → lowerBridgeFamily c = .C)) = true := by
      cases c <;> decide
    have hh : ∀ r ∈ lowerBridgeRecords c,
        (r.kind = .cLower ∨ r.kind = .cUpper) → lowerBridgeFamily c = .C := by
      simpa only [List.all_eq_true, decide_eq_true_eq] using hb
    exact hh r hr
  have hord : 0 < lowerBridgeDifference (lowerBridgeMatrices c (lowerInitialX n) (lowerInitialY k))
      r.upperWords r.lowerWords false →
      0 < (-1:ℝ)^(lowerBridgePair c n k).1.length *
        (prefixEval ((lowerBridgePair c n k).1++r.upperWords.1) lowerTau +
         prefixEval ((lowerBridgePair c n k).2++r.upperWords.2) lowerTau -
         prefixEval ((lowerBridgePair c n k).1++r.lowerWords.1) lowerTau -
         prefixEval ((lowerBridgePair c n k).2++r.lowerWords.2) lowerTau) := by
    intro hnum
    obtain ⟨s, hs, h1, h2⟩ := bridge_link c n k hm
    have hpar : (lowerBridgePair c n k).1.length % 2 = (lowerBridgePair c n k).2.length % 2 := hm.1
    exact contact_generic hfrac _ _ _ _ s hs h1 h2 false
      (by simpa using (pow_par _ _ hpar).symm) hnum
  have hcommon : (r.kind = .cLower ∨ r.kind = .cUpper) →
      0 < lowerBridgeDifference (lowerBridgeCommonMatrices c (lowerInitialX n) (lowerInitialY k))
        r.upperWords r.lowerWords true →
      0 < (-1:ℝ)^(lowerBridgeCommonPair c n k).1.length *
        (prefixEval ((lowerBridgeCommonPair c n k).1++r.upperWords.1) lowerTau +
         prefixEval ((lowerBridgeCommonPair c n k).2++r.upperWords.2) lowerTau -
         prefixEval ((lowerBridgeCommonPair c n k).1++r.lowerWords.1) lowerTau -
         prefixEval ((lowerBridgeCommonPair c n k).2++r.lowerWords.2) lowerTau) := by
    intro hrk hnum
    have hfc := hfamily hrk
    obtain ⟨s, hs, h1, h2⟩ := common_link c n k hc hfc
    have hlen : (lowerBridgeCommonPair c n k).1.length = (lowerBridgeCommonPair c n k).2.length + 3 := by
      simp only [lowerBridgeCommonPair, hfc, ite_true, List.length_append,
        List.length_cons, List.length_nil]
      omega
    have hpar : (-1:ℝ)^(lowerBridgeCommonPair c n k).2.length =
        -(-1:ℝ)^(lowerBridgeCommonPair c n k).1.length := by
      rw [hlen, pow_add]
      norm_num
    exact contact_generic hfrac _ _ _ _ s hs h1 h2 true (by simpa using hpar) hnum
  have hnum := hn r hr
  cases hkr : r.kind with
  | width => exact False.elim (hk.1 hkr)
  | auxiliary => exact False.elim (hk.2.1 hkr)
  | h7 => exact False.elim (hk.2.2.1 hkr)
  | notA9 => exact False.elim (hk.2.2.2 hkr)
  | fork =>
    simpa only [lowerBridgeRecordFact, hkr] using hord
      (by simpa only [lowerBridgeNumerator, hkr] using hnum)
  | chain =>
    simpa only [lowerBridgeRecordFact, hkr] using hord
      (by simpa only [lowerBridgeNumerator, hkr] using hnum)
  | lowerStrip =>
    simpa only [lowerBridgeRecordFact, hkr] using hord
      (by simpa only [lowerBridgeNumerator, hkr] using hnum)
  | upperStrip =>
    simpa only [lowerBridgeRecordFact, hkr] using hord
      (by simpa only [lowerBridgeNumerator, hkr] using hnum)
  | cLower =>
    simpa only [lowerBridgeRecordFact, hkr] using hcommon (Or.inl hkr)
      (by simpa only [lowerBridgeNumerator, hkr] using hnum)
  | cUpper =>
    simpa only [lowerBridgeRecordFact, hkr] using hcommon (Or.inr hkr)
      (by simpa only [lowerBridgeNumerator, hkr] using hnum)

#print axioms solution

example : (∀ (hfrac : ∀ (w : List ℕ+) (t : ℝ), 0 < t → prefixEval w t = lowerInitialMatEval (lowerInitialWordMatrix w) t ∧ 0 < lowerInitialMatDen (lowerInitialWordMatrix w) t ∧ (lowerInitialWordMatrix w).a*(lowerInitialWordMatrix w).d - (lowerInitialWordMatrix w).b*(lowerInitialWordMatrix w).c = (-1:ℝ)^w.length) (c : LowerBridgeCase) (n k : ℕ) (hc : lowerBridgeZero c = decide (n=0)) (hm : lowerInitialSeamLink (lowerBridgeSeamCase c) n (lowerBridgeK c k) 0) (hn : lowerBridgeNumeric c (lowerInitialX n) (lowerInitialY k)) (r : LowerBridgeRecord) (hr : r ∈ lowerBridgeRecords c) (hk : r.kind ≠ .width ∧ r.kind ≠ .auxiliary ∧ r.kind ≠ .h7 ∧ r.kind ≠ .notA9) ,  lowerBridgeRecordFact c n k r) := @solution
