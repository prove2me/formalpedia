-- Prove2me | solution 1 for Freiman.lower_entry_goodness_threeEven
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-12T21:27:44.69437+00:00
-- url     : https://prove2.me/submissions/3379825c-17da-4bb6-901a-48b56d2fd5a3

import Definitions.Def_Freiman_lowerCertificates
import Definitions.Def_Freiman_lowerCover
import Definitions.Def_Freiman_lowerInitial
import Definitions.Def_Freiman_lowerInitialEntry
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Theorems.Thm_Freiman_continuant_denominator_pos
import Theorems.Thm_Freiman_prefixEval_difference
import Theorems.Thm_Freiman_trunk_endpoint_strict_order
open Freiman
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace VerifiedEntryTransfers
set_option autoImplicit true
set_option maxHeartbeats 5000000

open Freiman

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

private theorem tails :
    lowerAlpha ∈ Set.Icc (0 : ℝ) 1 ∧
    lowerBeta ∈ Set.Icc (0 : ℝ) 1 ∧ lowerAlpha < lowerBeta := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 21)
  have hn := Real.sqrt_nonneg (21 : ℝ)
  have hlo : 3 < Real.sqrt (21 : ℝ) := by nlinarith
  have hhi : Real.sqrt (21 : ℝ) < 5 := by nlinarith
  dsimp [lowerAlpha, lowerBeta, Set.mem_Icc]
  constructor
  · constructor <;> linarith
  constructor
  · constructor <;> linarith
  · linarith

private theorem width_formula (w : List ℕ+) :
    lowerWidth w = (lowerBeta - lowerAlpha) /
      ((((lowerCD w).1 : ℝ) * lowerAlpha + (lowerCD w).2) *
       (((lowerCD w).1 : ℝ) * lowerBeta + (lowerCD w).2)) := by
  unfold lowerWidth
  rw [prefixEval_difference w lowerBeta lowerAlpha tails.2.1 tails.1]
  rw [abs_of_pos (sub_pos.mpr tails.2.2), cd_eq]
  ring

private theorem width_pos (w : List ℕ+) : 0 < lowerWidth w := by
  rw [width_formula]
  have hq := q_pos w
  have ha : 0 ≤ lowerAlpha := tails.1.1
  have hb : 0 ≤ lowerBeta := tails.2.1.1
  exact div_pos (sub_pos.mpr tails.2.2) (mul_pos (by positivity) (by positivity))

private theorem width_lt_of_cd (u v : List ℕ+)
    (hc : ((lowerCD u).1 : ℝ) ≤ ((lowerCD v).1 : ℝ))
    (hd : ((lowerCD u).2 : ℝ) < ((lowerCD v).2 : ℝ)) :
    lowerWidth v < lowerWidth u := by
  rw [width_formula v, width_formula u]
  have ha : 0 ≤ lowerAlpha := tails.1.1
  have hb : 0 ≤ lowerBeta := tails.2.1.1
  have hdu := q_pos u
  have hdv := q_pos v
  have hA : ((lowerCD u).1 : ℝ) * lowerAlpha + (lowerCD u).2 <
      ((lowerCD v).1 : ℝ) * lowerAlpha + (lowerCD v).2 := by
    have hmul := mul_nonneg (sub_nonneg.mpr hc) ha
    nlinarith
  have hB : ((lowerCD u).1 : ℝ) * lowerBeta + (lowerCD u).2 <
      ((lowerCD v).1 : ℝ) * lowerBeta + (lowerCD v).2 := by
    have hmul := mul_nonneg (sub_nonneg.mpr hc) hb
    nlinarith
  have hAu : 0 < ((lowerCD u).1 : ℝ) * lowerAlpha + (lowerCD u).2 := by positivity
  have hAv : 0 < ((lowerCD v).1 : ℝ) * lowerAlpha + (lowerCD v).2 := by positivity
  have hBu : 0 < ((lowerCD u).1 : ℝ) * lowerBeta + (lowerCD u).2 := by positivity
  have hBv : 0 < ((lowerCD v).1 : ℝ) * lowerBeta + (lowerCD v).2 := by positivity
  have hden :
      (((lowerCD u).1 : ℝ) * lowerAlpha + (lowerCD u).2) *
        (((lowerCD u).1 : ℝ) * lowerBeta + (lowerCD u).2) <
      (((lowerCD v).1 : ℝ) * lowerAlpha + (lowerCD v).2) *
        (((lowerCD v).1 : ℝ) * lowerBeta + (lowerCD v).2) :=
    mul_lt_mul hA hB.le hBu hAv.le
  rw [div_lt_div_iff₀ (mul_pos hAv hBv) (mul_pos hAu hBu)]
  nlinarith [sub_pos.mpr tails.2.2]

private theorem cd_right_32 (w : List ℕ+) :
    lowerWidth (w ++ [3]) < lowerWidth (w ++ [2]) := by
  have h2 : lowerCD (w ++ [2]) = ((lowerCD w).2, (lowerCD w).1 + 2 * (lowerCD w).2) := by
    simp [lowerCD, List.foldl_append]
  have h3 : lowerCD (w ++ [3]) = ((lowerCD w).2, (lowerCD w).1 + 3 * (lowerCD w).2) := by
    simp [lowerCD, List.foldl_append]
  apply width_lt_of_cd
  · rw [h2, h3]
  · rw [h2, h3]
    push_cast
    nlinarith [q_pos w]

private theorem cd_right_3323 (w : List ℕ+) :
    lowerWidth (w ++ [3,3]) < lowerWidth (w ++ [2,3]) := by
  have h23 : lowerCD (w ++ [2,3]) =
      ((lowerCD w).1 + 2 * (lowerCD w).2, 3 * (lowerCD w).1 + 7 * (lowerCD w).2) := by
    simp [lowerCD, List.foldl_append]
    omega
  have h33 : lowerCD (w ++ [3,3]) =
      ((lowerCD w).1 + 3 * (lowerCD w).2, 3 * (lowerCD w).1 + 10 * (lowerCD w).2) := by
    simp [lowerCD, List.foldl_append]
    omega
  apply width_lt_of_cd
  · rw [h23, h33]
    push_cast
    have h0 : (0 : ℝ) ≤ ((lowerCD w).2 : ℝ) := by positivity
    nlinarith
  · rw [h23, h33]
    push_cast
    nlinarith [q_pos w]

private theorem cd_left_121_111 (w : List ℕ+) :
    lowerWidth (w ++ [1,2,1]) < lowerWidth (w ++ [1,1,1]) := by
  have h111 : lowerCD (w ++ [1,1,1]) =
      ((lowerCD w).1 + 2 * (lowerCD w).2, 2 * (lowerCD w).1 + 3 * (lowerCD w).2) := by
    simp [lowerCD, List.foldl_append]
    omega
  have h121 : lowerCD (w ++ [1,2,1]) =
      (2 * (lowerCD w).1 + 3 * (lowerCD w).2, 3 * (lowerCD w).1 + 4 * (lowerCD w).2) := by
    simp [lowerCD, List.foldl_append]
    omega
  apply width_lt_of_cd
  · rw [h111, h121]
    push_cast
    have h0c : (0 : ℝ) ≤ ((lowerCD w).1 : ℝ) := by positivity
    have h0d : (0 : ℝ) ≤ ((lowerCD w).2 : ℝ) := by positivity
    nlinarith
  · rw [h111, h121]
    push_cast
    nlinarith [q_pos w]

private theorem cd_left_1213_1113 (w : List ℕ+) :
    lowerWidth (w ++ [1,2,1,3]) < lowerWidth (w ++ [1,1,1,3]) := by
  have h1113 : lowerCD (w ++ [1,1,1,3]) =
      (2 * (lowerCD w).1 + 3 * (lowerCD w).2, 7 * (lowerCD w).1 + 11 * (lowerCD w).2) := by
    simp [lowerCD, List.foldl_append]
    omega
  have h1213 : lowerCD (w ++ [1,2,1,3]) =
      (3 * (lowerCD w).1 + 4 * (lowerCD w).2, 11 * (lowerCD w).1 + 15 * (lowerCD w).2) := by
    simp [lowerCD, List.foldl_append]
    omega
  apply width_lt_of_cd
  · rw [h1113, h1213]
    push_cast
    have h0c : (0 : ℝ) ≤ ((lowerCD w).1 : ℝ) := by positivity
    have h0d : (0 : ℝ) ≤ ((lowerCD w).2 : ℝ) := by positivity
    nlinarith
  · rw [h1113, h1213]
    push_cast
    nlinarith [q_pos w]
private theorem entry_width_transfers (p : LowerPair) (hv : lowerEntryVirtualNN p) :
    lowerWidth (p.2 ++ [1,1,1]) < lowerWidth (p.1 ++ [2]) ∧
    (7/5 : ℝ) * lowerWidth (p.2 ++ [1,1,1,3]) < lowerWidth (p.1 ++ [2,3]) ∧
    lowerWidth (p.2 ++ [1,2,1]) < lowerWidth (p.1 ++ [2]) ∧
    (7/5 : ℝ) * lowerWidth (p.2 ++ [1,2,1,3]) < lowerWidth (p.1 ++ [2,3]) ∧
    lowerWidth (p.2 ++ [1,1,1]) < lowerWidth (p.1 ++ [3]) ∧
    (7/5 : ℝ) * lowerWidth (p.2 ++ [1,1,1,3]) < lowerWidth (p.1 ++ [3,3]) ∧
    lowerWidth (p.2 ++ [1,2,1]) < lowerWidth (p.1 ++ [3]) ∧
    (7/5 : ℝ) * lowerWidth (p.2 ++ [1,2,1,3]) < lowerWidth (p.1 ++ [3,3]) := by
  rcases hv with ⟨hv1, hv2⟩
  have hp111 := width_pos (p.2 ++ [1,1,1])
  have hp1113 := width_pos (p.2 ++ [1,1,1,3])
  have h121 := cd_left_121_111 p.2
  have h1213 := cd_left_1213_1113 p.2
  have h32 := cd_right_32 p.1
  have h3323 := cd_right_3323 p.1
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith


end VerifiedEntryTransfers

namespace VerifiedEntryWidths
set_option autoImplicit true
set_option maxHeartbeats 5000000


open Freiman List

/-- One step of the continuant recursion. -/
private def cdF (z : ℕ × ℕ) (a : ℕ) : ℕ × ℕ := (z.2, z.1 + a * z.2)

/-- The explicit recursion equivalent to the left fold used by `lowerCD`. -/
private def cdGo : List ℕ → ℕ × ℕ → ℕ × ℕ
  | [], z => z
  | a :: as, z => cdGo as (cdF z a)

/-- The underlying digit list of a word. -/
private def dmap (w : List ℕ+) : List ℕ := do let a ← w; pure (a : ℕ)

private lemma dmap_nil : dmap [] = [] := rfl

private lemma dmap_cons (a : ℕ+) (w : List ℕ+) : dmap (a :: w) = ((a : ℕ) :: dmap w) := rfl

/-- The recursion computes the left fold. -/
private lemma cdGo_eq_foldl : ∀ (as : List ℕ) (z : ℕ × ℕ), cdGo as z = List.foldl cdF z as := by
  intro as
  induction as with
  | nil =>
    intro z
    rfl
  | cons a as ih =>
    intro z
    show cdGo as (cdF z a) = _
    rw [List.foldl_cons]
    exact ih (cdF z a)

/-- `lowerCD` is the explicit recursion started at `(0, 1)`. -/
private lemma lowerCD_eq (w : List ℕ+) : lowerCD w = cdGo (dmap w) ((0, 1) : ℕ × ℕ) := by
  show List.foldl (fun z a => (z.2, z.1 + (a : ℕ) * z.2)) (0, 1)
      (do let a ← w; pure (a : ℕ)) = cdGo (dmap w) ((0, 1) : ℕ × ℕ)
  unfold dmap
  exact (cdGo_eq_foldl (do let a ← w; pure (a : ℕ)) ((0, 1) : ℕ × ℕ)).symm

private lemma cdGo_append : ∀ (xs : List ℕ) (z : ℕ × ℕ) (ys : List ℕ),
      cdGo (xs ++ ys) z = cdGo ys (cdGo xs z) := by
  intro xs
  induction xs with
  | nil =>
    intro z ys
    rfl
  | cons a xs ih =>
    intro z ys
    show cdGo (xs ++ ys) (cdF z a) = cdGo ys (cdGo xs (cdF z a))
    exact ih (cdF z a) ys

private lemma dmap_append (u v : List ℕ+) : dmap (u ++ v) = dmap u ++ dmap v := by
  induction u with
  | nil => rfl
  | cons a u ih => simp only [List.cons_append, dmap_cons, ih]

/-- The continuants of a concatenated word. -/
private lemma lowerCD_append (u v : List ℕ+) :
    lowerCD (u ++ v) = cdGo (dmap v) (lowerCD u) := by
  rw [lowerCD_eq, dmap_append, cdGo_append, ← lowerCD_eq]

/-- Appending one digit applies the continuant step. -/
private lemma lowerCD_snoc (v : List ℕ+) (d : ℕ+) :
    lowerCD (v ++ [d]) = ((lowerCD v).2, (lowerCD v).1 + (d : ℕ) * (lowerCD v).2) := by
  rw [lowerCD_append]
  show cdGo (dmap ([d] : List ℕ+)) (lowerCD v) = _
  rw [show dmap ([d] : List ℕ+) = ((d : ℕ) :: []) by rw [dmap_cons, dmap_nil]]
  unfold cdGo
  rfl

/-! Next: evaluation along a word, and how it behaves when a digit is appended. -/

/-- Evaluating along a concatenation composes the evaluations. -/
private lemma prefixEval_append_lem : ∀ (w v : List ℕ+) (x : ℝ),
      prefixEval (w ++ v) x = prefixEval w (prefixEval v x) := by
  intro w
  induction w with
  | nil =>
    intro v x
    rfl
  | cons a w ih =>
    intro v x
    show 1 / ((a : ℝ) + prefixEval (w ++ v) x) = 1 / ((a : ℝ) + prefixEval w (prefixEval v x))
    rw [ih v x]

/-- Appending one digit evaluates through the Möbius map. -/
private lemma prefixEval_snoc (v : List ℕ+) (d : ℕ+) (x : ℝ) :
    prefixEval (v ++ [d]) x = prefixEval v (1 / ((d : ℝ) + x)) := by
  rw [prefixEval_append_lem]
  show prefixEval v (prefixEval ([d] : List ℕ+) x) = _
  congr 1

/-! The endpoints of the lower interval are positive and ordered. -/

private lemma sqrt21_gt_three : (3 : ℝ) < Real.sqrt 21 := Real.lt_sqrt_of_sq_lt (by norm_num)

private lemma lowerAlpha_pos : (0 : ℝ) < lowerAlpha := by
  have h := sqrt21_gt_three
  dsimp only [lowerAlpha]
  apply div_pos
  linarith
  norm_num

private lemma lowerBeta_pos : (0 : ℝ) < lowerBeta := by
  have h := sqrt21_gt_three
  dsimp only [lowerBeta]
  apply div_pos
  linarith
  norm_num

private lemma lowerAlpha_lt_beta : lowerAlpha < lowerBeta := by
  have h := sqrt21_gt_three
  dsimp only [lowerAlpha, lowerBeta]
  apply lt_of_sub_pos
  field_simp
  nlinarith

/-! The main difference identity. -/

/-- For positive arguments, the product of the difference of the two evaluations with the two
continuant denominators is the difference of the arguments. -/
private lemma prefixEval_diff : ∀ (w : List ℕ+), ∀ {x y : ℝ}, 0 < x → 0 < y →
      |prefixEval w x - prefixEval w y| * (((lowerCD w).1 : ℝ) * x + ((lowerCD w).2 : ℝ)) *
        (((lowerCD w).1 : ℝ) * y + ((lowerCD w).2 : ℝ)) = |x - y| := by
  intro w
  induction w using List.reverseRecOn with
  | nil =>
    intro x y hx hy
    have hpe (t : ℝ) : prefixEval ([] : List ℕ+) t = t := rfl
    have hc : lowerCD ([] : List ℕ+) = ((0, 1) : ℕ × ℕ) := rfl
    rw [hpe x, hpe y, hc]
    push_cast
    ring
  | append_singleton v d ih =>
    intro x y hx hy
    have hdx : (0 : ℝ) < (d : ℝ) + x := by positivity
    have hdy : (0 : ℝ) < (d : ℝ) + y := by positivity
    set X : ℝ := 1 / ((d : ℝ) + x) with hXdef
    set Y : ℝ := 1 / ((d : ℝ) + y) with hYdef
    set A : ℝ := ((lowerCD v).1 : ℝ) * X + ((lowerCD v).2 : ℝ) with hAdef
    set B : ℝ := ((lowerCD v).1 : ℝ) * Y + ((lowerCD v).2 : ℝ) with hBdef
    set Ux : ℝ := ((lowerCD (v ++ [d])).1 : ℝ) * x + ((lowerCD (v ++ [d])).2 : ℝ) with hUxdef
    set Uy : ℝ := ((lowerCD (v ++ [d])).1 : ℝ) * y + ((lowerCD (v ++ [d])).2 : ℝ) with hUydef
    have hXp : 0 < X := by rw [hXdef]; positivity
    have hYp : 0 < Y := by rw [hYdef]; positivity
    have hcu : ((lowerCD (v ++ [d])).1 : ℝ) = ((lowerCD v).2 : ℝ) := by
      rw [lowerCD_snoc v d]
    have hcv : ((lowerCD (v ++ [d])).2 : ℝ) =
        ((lowerCD v).1 : ℝ) + (d : ℝ) * ((lowerCD v).2 : ℝ) := by
      rw [lowerCD_snoc v d]
      push_cast
      ring
    have hfvx : prefixEval (v ++ [d]) x = prefixEval v X := by
      rw [prefixEval_snoc v d x, ← hXdef]
    have hfvy : prefixEval (v ++ [d]) y = prefixEval v Y := by
      rw [prefixEval_snoc v d y, ← hYdef]
    have hA : A * ((d : ℝ) + x) = Ux := by
      rw [hAdef, hUxdef, hcu, hcv, hXdef]
      field_simp
      ring
    have hB : B * ((d : ℝ) + y) = Uy := by
      rw [hBdef, hUydef, hcu, hcv, hYdef]
      field_simp
      ring
    have hXY : X - Y = (y - x) / (((d : ℝ) + x) * ((d : ℝ) + y)) := by
      rw [hXdef, hYdef]
      field_simp
      ring
    have hXY2 : |X - Y| * (((d : ℝ) + x) * ((d : ℝ) + y)) = |x - y| := by
      rw [hXY, abs_div, abs_mul, abs_of_pos hdx, abs_of_pos hdy, abs_sub_comm]
      field_simp
    have hv := @ih X Y hXp hYp
    rw [← hAdef, ← hBdef] at hv
    have hfvw : |prefixEval (v ++ [d]) x - prefixEval (v ++ [d]) y|
        = |prefixEval v X - prefixEval v Y| := by rw [hfvx, hfvy]
    rw [hfvw, ← hA, ← hB]
    rw [show |prefixEval v X - prefixEval v Y| * (A * ((d : ℝ) + x)) *
          (B * ((d : ℝ) + y))
        = (|prefixEval v X - prefixEval v Y| * A * B) * (((d : ℝ) + x) * ((d : ℝ) + y)) from by ring]
    rw [hv, hXY2]

/-- The second continuant of any word is at least one. -/
private lemma lowerCD_snd_ge_one : ∀ (w : List ℕ+), 1 ≤ (lowerCD w).2 := by
  intro w
  induction w using List.reverseRecOn with
  | nil =>
    have h0 : lowerCD ([] : List ℕ+) = ((0, 1) : ℕ × ℕ) := rfl
    rw [h0]
  | append_singleton u c ih =>
    rw [lowerCD_snoc u c]
    have hc : (1 : ℕ) ≤ (c : ℕ) := Nat.succ_le_of_lt (PNat.pos c)
    nlinarith [ih, Nat.zero_le ((lowerCD u).1)]

/-- The denominators are positive at positive arguments. -/
private lemma cdDen_pos (w : List ℕ+) {x : ℝ} (hx : 0 < x) :
    0 < ((lowerCD w).1 : ℝ) * x + ((lowerCD w).2 : ℝ) := by
  have h1 : (1 : ℝ) ≤ ((lowerCD w).2 : ℝ) := by exact_mod_cast (lowerCD_snd_ge_one w)
  have h0 : (0 : ℝ) ≤ ((lowerCD w).1 : ℝ) := by positivity
  nlinarith [mul_nonneg h0 hx.le]

/-- **Width formula.** -/
private theorem width_formula : ∀ (w : List ℕ+), lowerWidth w =
      (lowerBeta - lowerAlpha) /
        (((((lowerCD w).1 : ℝ) * lowerAlpha + ((lowerCD w).2 : ℝ)) *
          (((lowerCD w).1 : ℝ) * lowerBeta + ((lowerCD w).2 : ℝ)))) := by
  intro w
  have hwd : lowerWidth w = |prefixEval w lowerBeta - prefixEval w lowerAlpha| := rfl
  rw [hwd]
  set D : ℝ := |prefixEval w lowerBeta - prefixEval w lowerAlpha| with hDdef
  set P : ℝ := ((lowerCD w).1 : ℝ) * lowerAlpha + ((lowerCD w).2 : ℝ) with hPdef
  set Q : ℝ := ((lowerCD w).1 : ℝ) * lowerBeta + ((lowerCD w).2 : ℝ) with hQdef
  have hP : 0 < P := cdDen_pos w lowerAlpha_pos
  have hQ : 0 < Q := cdDen_pos w lowerBeta_pos
  have hd : D * Q * P = |lowerBeta - lowerAlpha| := by
    have := @prefixEval_diff w lowerBeta lowerAlpha lowerBeta_pos lowerAlpha_pos
    rwa [← hDdef, ← hPdef, ← hQdef] at this
  have hba : |lowerBeta - lowerAlpha| = lowerBeta - lowerAlpha :=
    abs_of_pos (by linarith [lowerAlpha_lt_beta])
  rw [hba] at hd
  rw [← hd]
  field_simp [hP, hQ]

/-! # Numeric pinning of the two kernels -/

private lemma alpha_bounds :
    (15825 / 60000 : ℝ) < lowerAlpha ∧ lowerAlpha < (15826 / 60000 : ℝ) := by
  have h : (4.5825 : ℝ) < Real.sqrt 21 ∧ Real.sqrt 21 < (4.5826 : ℝ) := by
    refine ⟨Real.lt_sqrt_of_sq_lt (by norm_num), ?_⟩
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (4.5826 : ℝ))]
    norm_num
  have h1 := h.1
  have h2 := h.2
  dsimp only [lowerAlpha]
  exact ⟨by linarith, by linarith⟩

private lemma beta_bounds :
    (15825 / 20000 : ℝ) < lowerBeta ∧ lowerBeta < (15826 / 20000 : ℝ) := by
  have h : (4.5825 : ℝ) < Real.sqrt 21 ∧ Real.sqrt 21 < (4.5826 : ℝ) := by
    refine ⟨Real.lt_sqrt_of_sq_lt (by norm_num), ?_⟩
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (4.5826 : ℝ))]
    norm_num
  have h1 := h.1
  have h2 := h.2
  dsimp only [lowerBeta]
  exact ⟨by linarith, by linarith⟩

noncomputable def Pi (t : ℝ) : ℝ := (lowerAlpha + t) * (lowerBeta + t)

noncomputable def Ps (t : ℝ) : ℝ := (t * lowerAlpha + 1) * (t * lowerBeta + 1)

/-- Rational envelopes for the two kernels. -/
noncomputable def PiLo (t : ℝ) : ℝ := ((15825 / 60000 : ℝ) + t) * ((15825 / 20000 : ℝ) + t)

noncomputable def PiHi (t : ℝ) : ℝ := ((15826 / 60000 : ℝ) + t) * ((15826 / 20000 : ℝ) + t)

noncomputable def PsLo (t : ℝ) : ℝ := ((t * (15825 / 60000 : ℝ)) + 1) * ((t * (15825 / 20000 : ℝ)) + 1)

noncomputable def PsHi (t : ℝ) : ℝ := ((t * (15826 / 60000 : ℝ)) + 1) * ((t * (15826 / 20000 : ℝ)) + 1)

private lemma Pi_lower {t : ℝ} (ht : (0 : ℝ) ≤ t) : PiLo t ≤ Pi t := by
  obtain ⟨ha, _⟩ := alpha_bounds
  obtain ⟨hb, _⟩ := beta_bounds
  dsimp only [PiLo, Pi]
  exact mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)

private lemma Pi_upper {t : ℝ} (ht : (0 : ℝ) ≤ t) : Pi t ≤ PiHi t := by
  obtain ⟨_, ha⟩ := alpha_bounds
  obtain ⟨_, hb⟩ := beta_bounds
  dsimp only [PiHi, Pi]
  exact mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)

private lemma Ps_lower {t : ℝ} (ht : (0 : ℝ) ≤ t) : PsLo t ≤ Ps t := by
  obtain ⟨ha, _⟩ := alpha_bounds
  obtain ⟨hb, _⟩ := beta_bounds
  dsimp only [PsLo, Ps]
  exact mul_le_mul (by nlinarith) (by nlinarith) (by positivity) (by positivity)

private lemma Ps_upper {t : ℝ} (ht : (0 : ℝ) ≤ t) : Ps t ≤ PsHi t := by
  obtain ⟨_, ha⟩ := alpha_bounds
  obtain ⟨_, hb⟩ := beta_bounds
  dsimp only [PsHi, Ps]
  exact mul_le_mul (by nlinarith) (by nlinarith) (by positivity) (by positivity)

private lemma Pi_mono {x y : ℝ} (hx : (0 : ℝ) ≤ x) (h : x ≤ y) : Pi x ≤ Pi y := by
  dsimp only [Pi]
  have h1 : lowerAlpha + x ≤ lowerAlpha + y := by linarith
  have h2 : lowerBeta + x ≤ lowerBeta + y := by linarith
  have h3 : (0 : ℝ) ≤ lowerAlpha + x := by linarith [lowerAlpha_pos]
  nlinarith [beta_bounds.1, lowerBeta_pos]

private lemma Ps_mono {x y : ℝ} (hx : (0 : ℝ) ≤ x) (h : x ≤ y) : Ps x ≤ Ps y := by
  dsimp only [Ps]
  have h1 : x * lowerAlpha ≤ y * lowerAlpha := mul_le_mul_of_nonneg_right h (lowerAlpha_pos.le)
  have h2 : x * lowerBeta ≤ y * lowerBeta := mul_le_mul_of_nonneg_right h (lowerBeta_pos.le)
  have h3 : (0 : ℝ) ≤ x * lowerAlpha + 1 := by nlinarith [lowerAlpha_pos]
  have h4 : (0 : ℝ) ≤ x * lowerBeta + 1 := by nlinarith [lowerBeta_pos]
  nlinarith

/-! The width in terms of the continuant denominator and the ratio. -/

/-- The second continuant of every word is at least one. -/
private lemma lowerCD_ge_one (w : List ℕ+) : (1 : ℝ) ≤ ((lowerCD w).2 : ℝ) := by
  exact_mod_cast (by
    have : ∀ (v : List ℕ+), 1 ≤ (lowerCD v).2 := by
      intro v
      induction v using List.reverseRecOn with
      | nil =>
        have h0 : lowerCD ([] : List ℕ+) = ((0, 1) : ℕ × ℕ) := rfl
        rw [h0]
      | append_singleton u c ih =>
        rw [lowerCD_snoc u c]
        have hc : (1 : ℕ) ≤ (c : ℕ) := Nat.succ_le_of_lt (PNat.pos c)
        nlinarith [ih, Nat.zero_le ((lowerCD u).1)]
    exact this w)

private lemma width_eq_ratio (v : List ℕ+) :
    lowerWidth v =
      (lowerBeta - lowerAlpha) / ((((lowerCD v).2 : ℝ) ^ 2) * Ps (lowerRatio v)) := by
  have hfw := width_formula v
  have hq : (1 : ℝ) ≤ ((lowerCD v).2 : ℝ) := lowerCD_ge_one v
  have hrho : lowerRatio v = ((lowerCD v).1 : ℝ) / ((lowerCD v).2 : ℝ) := rfl
  rw [hfw, hrho]
  dsimp only [Ps]
  have hne : ((lowerCD v).2 : ℝ) ≠ 0 := by linarith
  have hP : 0 < ((lowerCD v).1 : ℝ) * lowerAlpha + ((lowerCD v).2 : ℝ) := by
    have hu0 : (0 : ℝ) ≤ ((lowerCD v).1 : ℝ) := by positivity
    nlinarith [lowerAlpha_pos, hq]
  have hQ : 0 < ((lowerCD v).1 : ℝ) * lowerBeta + ((lowerCD v).2 : ℝ) := by
    have hu0 : (0 : ℝ) ≤ ((lowerCD v).1 : ℝ) := by positivity
    nlinarith [lowerBeta_pos, hq]
  field_simp [hne, hP.ne', hQ.ne'] <;> ring

private lemma width_append_digit (v : List ℕ+) (d : ℕ+) :
    lowerWidth (v ++ [d]) =
      (lowerBeta - lowerAlpha) / ((((lowerCD v).2 : ℝ) ^ 2) * Pi (lowerRatio v + (d : ℝ))) := by
  have hfw := width_formula (v ++ [d])
  have hsn := lowerCD_snoc v d
  have hq : (1 : ℝ) ≤ ((lowerCD v).2 : ℝ) := lowerCD_ge_one v
  have hrho : lowerRatio v = ((lowerCD v).1 : ℝ) / ((lowerCD v).2 : ℝ) := rfl
  rw [hfw]
  have hc1 : ((lowerCD (v ++ [d])).1 : ℝ) = ((lowerCD v).2 : ℝ) := by rw [hsn]
  have hc2 : ((lowerCD (v ++ [d])).2 : ℝ) =
      ((lowerCD v).1 : ℝ) + (d : ℝ) * ((lowerCD v).2 : ℝ) := by
    rw [hsn]
    push_cast
    ring
  rw [hc1, hc2, hrho]
  dsimp only [Pi]
  have hne : ((lowerCD v).2 : ℝ) ≠ 0 := by linarith
  have hA : 0 < ((lowerCD v).2 : ℝ) * lowerAlpha +
      ((lowerCD v).1 : ℝ) + (d : ℝ) * ((lowerCD v).2 : ℝ) := by
    have hu0 : (0 : ℝ) ≤ ((lowerCD v).1 : ℝ) := by positivity
    have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (PNat.pos d)
    nlinarith [lowerAlpha_pos, hq]
  have hB : 0 < ((lowerCD v).2 : ℝ) * lowerBeta +
      ((lowerCD v).1 : ℝ) + (d : ℝ) * ((lowerCD v).2 : ℝ) := by
    have hu0 : (0 : ℝ) ≤ ((lowerCD v).1 : ℝ) := by positivity
    have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (PNat.pos d)
    nlinarith [lowerBeta_pos, hq]
  field_simp [hne, hA.ne', hB.ne'] <;> ring

private lemma lowerChild_eq (r : LowerPair) (l : LowerLabel) :
    lowerChild r l = ((lowerNormalize r).1 ++ l.1.reverse, (lowerNormalize r).2 ++ l.2) := by
  dsimp only [lowerChild]

private lemma label_cases (l : LowerLabel) (hl : l ∈ lowerEntryLabels) :
    l = ([1], []) ∨ l = ([2], [1]) ∨ l = ([3], [1]) ∨ l = ([2], [2]) ∨ l = ([2], [3]) ∨
      l = ([3], [2]) := by
  revert hl
  simp only [lowerEntryLabels, List.mem_cons, List.mem_nil_iff, or_false]
  tauto

/-! Comparison helpers used by the six label cases. -/

private lemma cmp_Pi {σ x y lo hi : ℝ} (hσ : ((729 : ℝ) / 1024) < σ) (hlo : (0 : ℝ) ≤ lo)
    (hx : PiLo lo ≤ x) (hy : y ≤ PiHi hi)
    (hgap : PiHi hi < ((729 : ℝ) / 1024) * PiLo lo) : y < σ * x := by
  have hpos : 0 < PiLo lo := by dsimp only [PiLo]; positivity
  have hx' : 0 < x := lt_of_lt_of_le hpos hx
  have hσx : ((729 : ℝ) / 1024) * x < σ * x := mul_lt_mul_of_pos_right hσ hx'
  have hxc : ((729 : ℝ) / 1024) * PiLo lo ≤ ((729 : ℝ) / 1024) * x :=
    mul_le_mul_of_nonneg_left hx (by norm_num)
  nlinarith

private lemma cmp_Ps {σ x y lo hi : ℝ} (hσ : ((729 : ℝ) / 1024) < σ) (hlo : (0 : ℝ) ≤ lo)
    (hx : PiLo lo ≤ x) (hy : y ≤ PsHi hi)
    (hgap : PsHi hi < ((729 : ℝ) / 1024) * PiLo lo) : y < σ * x := by
  have hpos : 0 < PiLo lo := by dsimp only [PiLo]; positivity
  have hx' : 0 < x := lt_of_lt_of_le hpos hx
  have hσx : ((729 : ℝ) / 1024) * x < σ * x := mul_lt_mul_of_pos_right hσ hx'
  have hxc : ((729 : ℝ) / 1024) * PiLo lo ≤ ((729 : ℝ) / 1024) * x :=
    mul_le_mul_of_nonneg_left hx (by norm_num)
  nlinarith

private lemma cmp_rev {σ x y lo hi : ℝ} (hσ : σ < ((225 : ℝ) / 289)) (hy0 : (0 : ℝ) < y)
    (hx : PiLo lo ≤ x) (hy : y ≤ PiHi hi)
    (hgap : ((225 : ℝ) / 289) * PiHi hi < PiLo lo) : σ * y < x := by
  have hσy : σ * y < ((225 : ℝ) / 289) * y := mul_lt_mul_of_pos_right hσ hy0
  have hyc : ((225 : ℝ) / 289) * y ≤ ((225 : ℝ) / 289) * PiHi hi :=
    mul_le_mul_of_nonneg_left hy (by norm_num)
  nlinarith

/-- The four envelope functions are increasing on nonnegative arguments. -/
private lemma PiLo_mono {x y : ℝ} (hx : (0 : ℝ) ≤ x) (h : x ≤ y) : PiLo x ≤ PiLo y := by
  dsimp only [PiLo]
  nlinarith

private lemma PiHi_mono {x y : ℝ} (hx : (0 : ℝ) ≤ x) (h : x ≤ y) : PiHi x ≤ PiHi y := by
  dsimp only [PiHi]
  nlinarith

private lemma PsHi_mono {x y : ℝ} (hx : (0 : ℝ) ≤ x) (h : x ≤ y) : PsHi x ≤ PsHi y := by
  dsimp only [PsHi]
  have h1 : (0 : ℝ) ≤ x * (15826 / 60000 : ℝ) + 1 := by nlinarith
  nlinarith

/-- Lower bound for `Pi` at a shifted ratio. -/
private lemma Pi_shift_lower {ρ d l : ℝ} (hl : l ≤ ρ + d) (hlo : (0 : ℝ) ≤ l) : PiLo l ≤ Pi (ρ + d) :=
  le_trans (Pi_lower hlo) (Pi_mono hlo hl)

private lemma Pi_shift_upper {ρ d h' : ℝ} (hh : ρ + d ≤ h') (hd : (0 : ℝ) ≤ ρ + d) :
    Pi (ρ + d) ≤ PiHi h' := le_trans (Pi_upper hd) (PiHi_mono hd hh)

private lemma Ps_shift_upper {ρ h' : ℝ} (hh : ρ ≤ h') (hρ : (0 : ℝ) ≤ ρ) : Ps ρ ≤ PsHi h' :=
  le_trans (Ps_upper hρ) (PsHi_mono hρ hh)

private lemma Pi_pos {t : ℝ} (ht : (0 : ℝ) ≤ t) : 0 < Pi t := by
  dsimp only [Pi]
  apply mul_pos
  · nlinarith [lowerAlpha_pos, ht]
  · nlinarith [lowerBeta_pos, ht]

private lemma Ps_pos {t : ℝ} (ht : (0 : ℝ) ≤ t) : 0 < Ps t := by
  dsimp only [Ps]
  apply mul_pos
  · nlinarith [lowerAlpha_pos, ht]
  · nlinarith [lowerBeta_pos, ht]

/-- Two appended children: the first is narrower when the scale exceeds `729/1024`. -/
private lemma width_lt_append_append {σ : ℝ} {u₁ u₂ : List ℕ+} {d₁ d₂ : ℕ+}
    (hσ : ((729 : ℝ) / 1024) < σ) (hρ1 : (1 / 4 : ℝ) < lowerRatio u₁)
    (hρ2 : (1 / 4 : ℝ) < lowerRatio u₂) (hρ2' : lowerRatio u₂ < (4 / 13 : ℝ))
    (hscale : σ = ((lowerCD u₁).2 : ℝ) ^ 2 / ((lowerCD u₂).2 : ℝ) ^ 2)
    (hgap : PiHi ((d₂ : ℝ) + 4 / 13) < ((729 : ℝ) / 1024) * PiLo ((d₁ : ℝ) + 1 / 4)) :
    lowerWidth (u₁ ++ [d₁]) < lowerWidth (u₂ ++ [d₂]) := by
  rw [width_append_digit u₁ d₁, width_append_digit u₂ d₂]
  have hq1 : (0 : ℝ) < ((lowerCD u₁).2 : ℝ) := by linarith [lowerCD_ge_one u₁]
  have hq2 : (0 : ℝ) < ((lowerCD u₂).2 : ℝ) := by linarith [lowerCD_ge_one u₂]
  set q1 : ℝ := ((lowerCD u₁).2 : ℝ) ^ 2 with hq1def
  set q2 : ℝ := ((lowerCD u₂).2 : ℝ) ^ 2 with hq2def
  have hq1p : 0 < q1 := by rw [hq1def]; exact pow_pos hq1 2
  have hq2p : 0 < q2 := by rw [hq2def]; exact pow_pos hq2 2
  have ht1 : (0 : ℝ) ≤ lowerRatio u₁ + (d₁ : ℝ) := by
    have h₁ : (0 : ℝ) < lowerRatio u₁ := by linarith [hρ1]
    have h₂ : (0 : ℝ) ≤ ((d₁ : ℕ+) : ℝ) := by positivity
    nlinarith
  have ht2 : (0 : ℝ) ≤ lowerRatio u₂ + (d₂ : ℝ) := by
    have h₁ : (0 : ℝ) < lowerRatio u₂ := by linarith [hρ2]
    have h₂ : (0 : ℝ) ≤ ((d₂ : ℕ+) : ℝ) := by positivity
    nlinarith
  have hX : 0 < Pi (lowerRatio u₁ + (d₁ : ℝ)) := Pi_pos ht1
  have hY : 0 < Pi (lowerRatio u₂ + (d₂ : ℝ)) := Pi_pos ht2
  have hD1 : 0 < q1 * Pi (lowerRatio u₁ + (d₁ : ℝ)) := mul_pos hq1p hX
  have hD2 : 0 < q2 * Pi (lowerRatio u₂ + (d₂ : ℝ)) := mul_pos hq2p hY
  rw [div_lt_div_iff₀ hD1 hD2]
  have hXlo : PiLo ((d₁ : ℝ) + 1 / 4) ≤ Pi (lowerRatio u₁ + (d₁ : ℝ)) :=
    Pi_shift_lower (by nlinarith [hρ1]) (by positivity)
  have hYhi : Pi (lowerRatio u₂ + (d₂ : ℝ)) ≤ PiHi ((d₂ : ℝ) + 4 / 13) :=
    Pi_shift_upper (by nlinarith [hρ2']) (by nlinarith [hρ2])
  have hgap' : PiHi ((d₂ : ℝ) + 4 / 13) < ((729 : ℝ) / 1024) * PiLo ((d₁ : ℝ) + 1 / 4) := hgap
  have hcmp : Pi (lowerRatio u₂ + (d₂ : ℝ)) < σ * Pi (lowerRatio u₁ + (d₁ : ℝ)) :=
    cmp_Pi hσ (by positivity) hXlo hYhi hgap'
  have hmul : q2 * σ = q1 := by
    rw [hscale]
    field_simp [hq2p.ne']
  have hba : (0 : ℝ) < lowerBeta - lowerAlpha := by linarith [lowerAlpha_lt_beta]
  have hgoal : q2 * Pi (lowerRatio u₂ + (d₂ : ℝ)) < q1 * Pi (lowerRatio u₁ + (d₁ : ℝ)) := by
    calc q2 * Pi (lowerRatio u₂ + (d₂ : ℝ)) < q2 * (σ * Pi (lowerRatio u₁ + (d₁ : ℝ))) :=
        mul_lt_mul_of_pos_left hcmp hq2p
      _ = q2 * σ * Pi (lowerRatio u₁ + (d₁ : ℝ)) := by ring
      _ = q1 * Pi (lowerRatio u₁ + (d₁ : ℝ)) := by rw [hmul]
  have hfinal : (lowerBeta - lowerAlpha) * (q2 * Pi (lowerRatio u₂ + (d₂ : ℝ))) <
      (lowerBeta - lowerAlpha) * (q1 * Pi (lowerRatio u₁ + (d₁ : ℝ))) :=
    mul_lt_mul_of_pos_left hgoal hba
  convert hfinal using 1 <;> ring

/-- The first child with no appended digit: `Ψ` appears on that side. -/
private lemma width_lt_append_none {σ : ℝ} {u₁ u₂ : List ℕ+} {d₁ : ℕ+}
    (hσ : ((729 : ℝ) / 1024) < σ) (hρ1 : (1 / 4 : ℝ) < lowerRatio u₁)
    (hρ2 : (1 / 4 : ℝ) < lowerRatio u₂) (hρ2' : lowerRatio u₂ < (4 / 13 : ℝ))
    (hscale : σ = ((lowerCD u₁).2 : ℝ) ^ 2 / ((lowerCD u₂).2 : ℝ) ^ 2)
    (hgap : PsHi (4 / 13) < ((729 : ℝ) / 1024) * PiLo ((d₁ : ℝ) + 1 / 4)) :
    lowerWidth (u₁ ++ [d₁]) < lowerWidth u₂ := by
  rw [width_append_digit u₁ d₁, width_eq_ratio u₂]
  have hq1 : (0 : ℝ) < ((lowerCD u₁).2 : ℝ) := by linarith [lowerCD_ge_one u₁]
  have hq2 : (0 : ℝ) < ((lowerCD u₂).2 : ℝ) := by linarith [lowerCD_ge_one u₂]
  set q1 : ℝ := ((lowerCD u₁).2 : ℝ) ^ 2 with hq1def
  set q2 : ℝ := ((lowerCD u₂).2 : ℝ) ^ 2 with hq2def
  have hq1p : 0 < q1 := by rw [hq1def]; exact pow_pos hq1 2
  have hq2p : 0 < q2 := by rw [hq2def]; exact pow_pos hq2 2
  have ht1 : (0 : ℝ) ≤ lowerRatio u₁ + (d₁ : ℝ) := by
    have h₁ : (0 : ℝ) < lowerRatio u₁ := by linarith [hρ1]
    have h₂ : (0 : ℝ) ≤ ((d₁ : ℕ+) : ℝ) := by positivity
    nlinarith
  have ht2 : (0 : ℝ) ≤ lowerRatio u₂ := by linarith [hρ2]
  have hX : 0 < Pi (lowerRatio u₁ + (d₁ : ℝ)) := Pi_pos ht1
  have hY : 0 < Ps (lowerRatio u₂) := Ps_pos ht2
  have hD1 : 0 < q1 * Pi (lowerRatio u₁ + (d₁ : ℝ)) := mul_pos hq1p hX
  have hD2 : 0 < q2 * Ps (lowerRatio u₂) := mul_pos hq2p hY
  rw [div_lt_div_iff₀ hD1 hD2]
  have hXlo : PiLo ((d₁ : ℝ) + 1 / 4) ≤ Pi (lowerRatio u₁ + (d₁ : ℝ)) :=
    Pi_shift_lower (by nlinarith [hρ1]) (by positivity)
  have hYhi : Ps (lowerRatio u₂) ≤ PsHi (4 / 13) :=
    Ps_shift_upper (by linarith [hρ2']) ht2
  have hgap' : PsHi (4 / 13) < ((729 : ℝ) / 1024) * PiLo ((d₁ : ℝ) + 1 / 4) := hgap
  have hcmp : Ps (lowerRatio u₂) < σ * Pi (lowerRatio u₁ + (d₁ : ℝ)) :=
    cmp_Ps hσ (by positivity) hXlo hYhi hgap'
  have hmul : q2 * σ = q1 := by
    rw [hscale]
    field_simp [hq2p.ne']
  have hba : (0 : ℝ) < lowerBeta - lowerAlpha := by linarith [lowerAlpha_lt_beta]
  have hgoal : q2 * Ps (lowerRatio u₂) < q1 * Pi (lowerRatio u₁ + (d₁ : ℝ)) := by
    calc q2 * Ps (lowerRatio u₂) < q2 * (σ * Pi (lowerRatio u₁ + (d₁ : ℝ))) :=
        mul_lt_mul_of_pos_left hcmp hq2p
      _ = q2 * σ * Pi (lowerRatio u₁ + (d₁ : ℝ)) := by ring
      _ = q1 * Pi (lowerRatio u₁ + (d₁ : ℝ)) := by rw [hmul]
  have hfinal : (lowerBeta - lowerAlpha) * (q2 * Ps (lowerRatio u₂)) <
      (lowerBeta - lowerAlpha) * (q1 * Pi (lowerRatio u₁ + (d₁ : ℝ))) :=
    mul_lt_mul_of_pos_left hgoal hba
  convert hfinal using 1 <;> ring

/-- Reversed orientation for the two exceptional labels. -/
private lemma width_lt_rev {σ : ℝ} {u₁ u₂ : List ℕ+} {d₁ d₂ : ℕ+}
    (hσ : σ < ((225 : ℝ) / 289)) (hρ1 : (1 / 4 : ℝ) < lowerRatio u₁)
    (hρ1' : lowerRatio u₁ < (9 / 25 : ℝ)) (hρ2 : (1 / 4 : ℝ) < lowerRatio u₂)
    (hscale : σ = ((lowerCD u₁).2 : ℝ) ^ 2 / ((lowerCD u₂).2 : ℝ) ^ 2)
    (hgap : ((225 : ℝ) / 289) * PiHi ((d₁ : ℝ) + 9 / 25) < PiLo ((d₂ : ℝ) + 1 / 4)) :
    lowerWidth (u₂ ++ [d₂]) < lowerWidth (u₁ ++ [d₁]) := by
  rw [width_append_digit u₂ d₂, width_append_digit u₁ d₁]
  have hq1 : (0 : ℝ) < ((lowerCD u₁).2 : ℝ) := by linarith [lowerCD_ge_one u₁]
  have hq2 : (0 : ℝ) < ((lowerCD u₂).2 : ℝ) := by linarith [lowerCD_ge_one u₂]
  set q1 : ℝ := ((lowerCD u₁).2 : ℝ) ^ 2 with hq1def
  set q2 : ℝ := ((lowerCD u₂).2 : ℝ) ^ 2 with hq2def
  have hq1p : 0 < q1 := by rw [hq1def]; exact pow_pos hq1 2
  have hq2p : 0 < q2 := by rw [hq2def]; exact pow_pos hq2 2
  have ht1 : (0 : ℝ) ≤ lowerRatio u₁ + (d₁ : ℝ) := by
    have h₁ : (0 : ℝ) < lowerRatio u₁ := by linarith [hρ1]
    have h₂ : (0 : ℝ) ≤ ((d₁ : ℕ+) : ℝ) := by positivity
    nlinarith
  have ht2 : (0 : ℝ) ≤ lowerRatio u₂ + (d₂ : ℝ) := by
    have h₁ : (0 : ℝ) < lowerRatio u₂ := by linarith [hρ2]
    have h₂ : (0 : ℝ) ≤ ((d₂ : ℕ+) : ℝ) := by positivity
    nlinarith
  have hX : 0 < Pi (lowerRatio u₂ + (d₂ : ℝ)) := Pi_pos ht2
  have hY : 0 < Pi (lowerRatio u₁ + (d₁ : ℝ)) := Pi_pos ht1
  have hD1 : 0 < q2 * Pi (lowerRatio u₂ + (d₂ : ℝ)) := mul_pos hq2p hX
  have hD2 : 0 < q1 * Pi (lowerRatio u₁ + (d₁ : ℝ)) := mul_pos hq1p hY
  rw [div_lt_div_iff₀ hD1 hD2]
  have hXlo : PiLo ((d₂ : ℝ) + 1 / 4) ≤ Pi (lowerRatio u₂ + (d₂ : ℝ)) :=
    Pi_shift_lower (by nlinarith [hρ2]) (by positivity)
  have hYhi : Pi (lowerRatio u₁ + (d₁ : ℝ)) ≤ PiHi ((d₁ : ℝ) + 9 / 25) :=
    Pi_shift_upper (by nlinarith [hρ1']) (by nlinarith [hρ1])
  have hcmp : σ * Pi (lowerRatio u₁ + (d₁ : ℝ)) < Pi (lowerRatio u₂ + (d₂ : ℝ)) :=
    cmp_rev hσ hY hXlo hYhi hgap
  have hmul : q2 * σ = q1 := by
    rw [hscale]
    field_simp [hq2p.ne']
  have hba : (0 : ℝ) < lowerBeta - lowerAlpha := by linarith [lowerAlpha_lt_beta]
  have hgoal : q1 * Pi (lowerRatio u₁ + (d₁ : ℝ)) < q2 * Pi (lowerRatio u₂ + (d₂ : ℝ)) := by
    calc q1 * Pi (lowerRatio u₁ + (d₁ : ℝ)) = q2 * σ * Pi (lowerRatio u₁ + (d₁ : ℝ)) := by rw [hmul]
      _ = q2 * (σ * Pi (lowerRatio u₁ + (d₁ : ℝ))) := by ring
      _ < q2 * Pi (lowerRatio u₂ + (d₂ : ℝ)) := mul_lt_mul_of_pos_left hcmp hq2p
  have hfinal : (lowerBeta - lowerAlpha) * (q1 * Pi (lowerRatio u₁ + (d₁ : ℝ))) <
      (lowerBeta - lowerAlpha) * (q2 * Pi (lowerRatio u₂ + (d₂ : ℝ))) :=
    mul_lt_mul_of_pos_left hgoal hba
  convert hfinal using 1 <;> ring

private theorem entry_child_orientation_closed (p : LowerPair) (hd : lowerEntryDomain p) (hn : lowerNormalize p = p) :
    lowerEntryChildOrientation p := by
  intro l hl
  have hs1 : ((729 : ℝ) / 1024) < lowerScale p := hd.1
  have hs2 : lowerScale p < ((225 : ℝ) / 289) := hd.2.1
  have h1lo : (1 / 4 : ℝ) < lowerRatio p.1 := hd.2.2.1
  have h1hi : lowerRatio p.1 < (9 / 25 : ℝ) := hd.2.2.2.1
  have h2lo : (1 / 4 : ℝ) < lowerRatio p.2 := hd.2.2.2.2.1
  have h2hi : lowerRatio p.2 < (4 / 13 : ℝ) := hd.2.2.2.2.2
  have hba : (0 : ℝ) < lowerBeta - lowerAlpha := by linarith [lowerAlpha_lt_beta]
  have hq1 : (0 : ℝ) < ((lowerCD p.1).2 : ℝ) := by
    have := lowerCD_ge_one p.1
    linarith
  have hq2 : (0 : ℝ) < ((lowerCD p.2).2 : ℝ) := by
    have := lowerCD_ge_one p.2
    linarith
  rcases label_cases l hl with rfl | rfl | rfl | rfl | rfl | rfl
  · -- label ([1], [])
    have hc : lowerChild p (([1] : List ℕ+), ([] : List ℕ+)) = (p.1 ++ [1], p.2) := by
      rw [lowerChild_eq, hn]
      dsimp only [Prod.fst, Prod.snd]
      simp only [List.reverse_cons, List.reverse_nil, List.append_nil, List.nil_append]
    have hcond : ¬ ((([1] : List ℕ+), ([] : List ℕ+)) = (([2] : List ℕ+), ([2] : List ℕ+)) ∨
        (([1] : List ℕ+), ([] : List ℕ+)) = (([2] : List ℕ+), ([3] : List ℕ+))) := by
      simp only [Prod.mk.injEq]
      norm_num
    rw [hc, if_neg hcond]
    rw [width_append_digit p.1 (1 : ℕ+), width_eq_ratio p.2]
    have hco1 : ((1 : ℕ+) : ℝ) = (1 : ℝ) := by norm_num
    rw [hco1]
    set q1 : ℝ := ((lowerCD p.1).2 : ℝ) ^ 2 with hq1def
    set q2 : ℝ := ((lowerCD p.2).2 : ℝ) ^ 2 with hq2def
    have hq1p : 0 < q1 := by rw [hq1def]; exact pow_pos hq1 2
    have hq2p : 0 < q2 := by rw [hq2def]; exact pow_pos hq2 2
    have hX : 0 < Pi (lowerRatio p.1 + 1) := by
      dsimp only [Pi]
      apply mul_pos
      · nlinarith [lowerAlpha_pos, h1lo]
      · nlinarith [lowerBeta_pos, h1lo]
    have hY : 0 < Ps (lowerRatio p.2) := by
      dsimp only [Ps]
      apply mul_pos
      · nlinarith [lowerAlpha_pos, h2lo]
      · nlinarith [lowerBeta_pos, h2lo]
    have hD1 : 0 < q1 * Pi (lowerRatio p.1 + 1) := mul_pos hq1p hX
    have hD2 : 0 < q2 * Ps (lowerRatio p.2) := mul_pos hq2p hY
    rw [div_lt_div_iff₀ hD1 hD2]
    have hscale : lowerScale p = q1 / q2 := by
      dsimp only [lowerScale]
    have hXlo : PiLo (5 / 4) ≤ Pi (lowerRatio p.1 + 1) :=
      Pi_shift_lower (by linarith [h1lo]) (by positivity)
    have hYhi : Ps (lowerRatio p.2) ≤ PsHi (4 / 13) :=
      Ps_shift_upper (by linarith [h2hi]) (by positivity)
    have hgap : PsHi (4 / 13) < ((729 : ℝ) / 1024) * PiLo (5 / 4) := by
      dsimp only [PsHi, PiLo]
      norm_num
    have hcmp : Ps (lowerRatio p.2) < lowerScale p * Pi (lowerRatio p.1 + 1) :=
      cmp_Ps hs1 (by positivity) hXlo hYhi hgap
    have hmul : q2 * lowerScale p = q1 := by
      dsimp only [q1, q2, lowerScale]
      field_simp
    have hgoal : q2 * Ps (lowerRatio p.2) < q1 * Pi (lowerRatio p.1 + 1) := by
      calc q2 * Ps (lowerRatio p.2) < q2 * (lowerScale p * Pi (lowerRatio p.1 + 1)) :=
          mul_lt_mul_of_pos_left hcmp hq2p
        _ = q2 * lowerScale p * Pi (lowerRatio p.1 + 1) := by ring
        _ = q1 * Pi (lowerRatio p.1 + 1) := by rw [hmul]
    have hfinal : (lowerBeta - lowerAlpha) * (q2 * Ps (lowerRatio p.2)) <
        (lowerBeta - lowerAlpha) * (q1 * Pi (lowerRatio p.1 + 1)) :=
      mul_lt_mul_of_pos_left hgoal hba
    convert hfinal using 1 <;> ring
  · -- label ([2], [1])
    have hc : lowerChild p (([2] : List ℕ+), ([1] : List ℕ+)) =
        (p.1 ++ [2], p.2 ++ [1]) := by
      rw [lowerChild_eq, hn]
      dsimp only [Prod.fst, Prod.snd]
      simp only [List.reverse_cons, List.reverse_nil, List.append_nil, List.nil_append]
    have hcond : ¬ ((([2] : List ℕ+), ([1] : List ℕ+)) = (([2] : List ℕ+), ([2] : List ℕ+)) ∨
        (([2] : List ℕ+), ([1] : List ℕ+)) = (([2] : List ℕ+), ([3] : List ℕ+))) := by
      simp only [Prod.mk.injEq]
      norm_num
    rw [hc, if_neg hcond]
    refine width_lt_append_append hs1 h1lo h2lo h2hi ?_ ?_
    · rfl
    · dsimp only [PiHi, PiLo]
      norm_num
  · -- label ([3], [1])
    have hc : lowerChild p (([3] : List ℕ+), ([1] : List ℕ+)) =
        (p.1 ++ [3], p.2 ++ [1]) := by
      rw [lowerChild_eq, hn]
      dsimp only [Prod.fst, Prod.snd]
      simp only [List.reverse_cons, List.reverse_nil, List.append_nil, List.nil_append]
    have hcond : ¬ ((([3] : List ℕ+), ([1] : List ℕ+)) = (([2] : List ℕ+), ([2] : List ℕ+)) ∨
        (([3] : List ℕ+), ([1] : List ℕ+)) = (([2] : List ℕ+), ([3] : List ℕ+))) := by
      simp only [Prod.mk.injEq]
      norm_num
    rw [hc, if_neg hcond]
    refine width_lt_append_append hs1 h1lo h2lo h2hi ?_ ?_
    · rfl
    · dsimp only [PiHi, PiLo]
      norm_num
  · -- label ([2], [2]) : the exceptional orientation
    have hc : lowerChild p (([2] : List ℕ+), ([2] : List ℕ+)) =
        (p.1 ++ [2], p.2 ++ [2]) := by
      rw [lowerChild_eq, hn]
      dsimp only [Prod.fst, Prod.snd]
      simp only [List.reverse_cons, List.reverse_nil, List.append_nil, List.nil_append]
    have hcond : ((([2] : List ℕ+), ([2] : List ℕ+)) = (([2] : List ℕ+), ([2] : List ℕ+)) ∨
        (([2] : List ℕ+), ([2] : List ℕ+)) = (([2] : List ℕ+), ([3] : List ℕ+))) := by
      left
      rfl
    rw [hc, if_pos hcond]
    refine width_lt_rev hs2 h1lo h1hi h2lo ?_ ?_
    · rfl
    · dsimp only [PiHi, PiLo]
      norm_num
  · -- label ([2], [3]) : the exceptional orientation
    have hc : lowerChild p (([2] : List ℕ+), ([3] : List ℕ+)) =
        (p.1 ++ [2], p.2 ++ [3]) := by
      rw [lowerChild_eq, hn]
      dsimp only [Prod.fst, Prod.snd]
      simp only [List.reverse_cons, List.reverse_nil, List.append_nil, List.nil_append]
    have hcond : ((([2] : List ℕ+), ([3] : List ℕ+)) = (([2] : List ℕ+), ([2] : List ℕ+)) ∨
        (([2] : List ℕ+), ([3] : List ℕ+)) = (([2] : List ℕ+), ([3] : List ℕ+))) := by
      right
      rfl
    rw [hc, if_pos hcond]
    refine width_lt_rev hs2 h1lo h1hi h2lo ?_ ?_
    · rfl
    · dsimp only [PiHi, PiLo]
      norm_num
  · -- label ([3], [2])
    have hc : lowerChild p (([3] : List ℕ+), ([2] : List ℕ+)) =
        (p.1 ++ [3], p.2 ++ [2]) := by
      rw [lowerChild_eq, hn]
      dsimp only [Prod.fst, Prod.snd]
      simp only [List.reverse_cons, List.reverse_nil, List.append_nil, List.nil_append]
    have hcond : ¬ ((([3] : List ℕ+), ([2] : List ℕ+)) = (([2] : List ℕ+), ([2] : List ℕ+)) ∨
        (([3] : List ℕ+), ([2] : List ℕ+)) = (([2] : List ℕ+), ([3] : List ℕ+))) := by
      simp only [Prod.mk.injEq]
      norm_num
    rw [hc, if_neg hcond]
    refine width_lt_append_append hs1 h1lo h2lo h2hi ?_ ?_
    · rfl
    · dsimp only [PiHi, PiLo]
      norm_num


private lemma width_lt_append_append_three {σ : ℝ}
    {u₁ u₂ : List ℕ+} {d₁ d₂ : ℕ+}
    (hk : (3 : ℝ) < σ) (hρ1 : (1 / 4 : ℝ) < lowerRatio u₁)
    (hρ2 : (1 / 4 : ℝ) < lowerRatio u₂) (hρ2' : lowerRatio u₂ < (4 / 13 : ℝ))
    (hscale : σ = ((lowerCD u₁).2 : ℝ) ^ 2 / ((lowerCD u₂).2 : ℝ) ^ 2)
    (hgap : PiHi ((d₂ : ℝ) + 4 / 13) < 3 * PiLo ((d₁ : ℝ) + 1 / 4)) :
    lowerWidth (u₁ ++ [d₁]) < lowerWidth (u₂ ++ [d₂]) := by
  rw [width_append_digit u₁ d₁, width_append_digit u₂ d₂]
  have hq1 : (0 : ℝ) < ((lowerCD u₁).2 : ℝ) := by linarith [lowerCD_ge_one u₁]
  have hq2 : (0 : ℝ) < ((lowerCD u₂).2 : ℝ) := by linarith [lowerCD_ge_one u₂]
  set q1 : ℝ := ((lowerCD u₁).2 : ℝ) ^ 2
  set q2 : ℝ := ((lowerCD u₂).2 : ℝ) ^ 2
  have hq1p : 0 < q1 := sq_pos_of_pos hq1
  have hq2p : 0 < q2 := sq_pos_of_pos hq2
  have ht1 : (0 : ℝ) ≤ lowerRatio u₁ + (d₁ : ℝ) := by positivity
  have ht2 : (0 : ℝ) ≤ lowerRatio u₂ + (d₂ : ℝ) := by positivity
  have hX := Pi_pos ht1
  have hY := Pi_pos ht2
  rw [div_lt_div_iff₀ (mul_pos hq1p hX) (mul_pos hq2p hY)]
  have hXlo : PiLo ((d₁ : ℝ) + 1 / 4) ≤ Pi (lowerRatio u₁ + (d₁ : ℝ)) :=
    Pi_shift_lower (by nlinarith [hρ1]) (by positivity)
  have hYhi : Pi (lowerRatio u₂ + (d₂ : ℝ)) ≤ PiHi ((d₂ : ℝ) + 4 / 13) :=
    Pi_shift_upper (by nlinarith [hρ2']) (by nlinarith [hρ2])
  have hPiLo : 0 < PiLo ((d₁ : ℝ) + 1 / 4) := by
    dsimp only [PiLo]
    positivity
  have hcmp : Pi (lowerRatio u₂ + (d₂ : ℝ)) <
      σ * Pi (lowerRatio u₁ + (d₁ : ℝ)) := by
    have hkx : 3 * PiLo ((d₁ : ℝ) + 1 / 4) <
        σ * PiLo ((d₁ : ℝ) + 1 / 4) := mul_lt_mul_of_pos_right hk hPiLo
    have hsx : σ * PiLo ((d₁ : ℝ) + 1 / 4) ≤
        σ * Pi (lowerRatio u₁ + (d₁ : ℝ)) := by
      have hσ0 : 0 < σ := lt_trans (by norm_num : (0 : ℝ) < 3) hk
      exact mul_le_mul_of_nonneg_left hXlo hσ0.le
    exact lt_of_le_of_lt hYhi (lt_of_lt_of_le (lt_trans hgap hkx) hsx)
  have hmul : q2 * σ = q1 := by
    rw [hscale]
    dsimp only [q1, q2]
    field_simp [hq2p.ne']
  have hgoal : q2 * Pi (lowerRatio u₂ + (d₂ : ℝ)) <
      q1 * Pi (lowerRatio u₁ + (d₁ : ℝ)) := by
    calc
      _ < q2 * (σ * Pi (lowerRatio u₁ + (d₁ : ℝ))) := mul_lt_mul_of_pos_left hcmp hq2p
      _ = q1 * Pi (lowerRatio u₁ + (d₁ : ℝ)) := by rw [← mul_assoc, hmul]
  have hba : 0 < lowerBeta - lowerAlpha := sub_pos.mpr lowerAlpha_lt_beta
  have hfinal : (lowerBeta - lowerAlpha) *
      (q2 * Pi (lowerRatio u₂ + (d₂ : ℝ))) <
      (lowerBeta - lowerAlpha) *
      (q1 * Pi (lowerRatio u₁ + (d₁ : ℝ))) :=
    mul_lt_mul_of_pos_left hgoal hba
  convert hfinal using 1 <;> ring
private theorem corrected_grandchild_widths (p : LowerPair) (hd : lowerEntryDomain p) :
    lowerWidth (p.1 ++ [2,1]) < lowerWidth (p.2 ++ [2]) ∧
    lowerWidth (p.1 ++ [2,2]) < lowerWidth (p.2 ++ [2]) ∧
    lowerWidth (p.1 ++ [2,2]) < lowerWidth (p.2 ++ [3]) := by
  have hs1 : ((729 : ℝ) / 1024) < lowerScale p := hd.1
  have h1lo : (1 / 4 : ℝ) < lowerRatio p.1 := hd.2.2.1
  have h1hi : lowerRatio p.1 < (9 / 25 : ℝ) := hd.2.2.2.1
  have h2lo : (1 / 4 : ℝ) < lowerRatio p.2 := hd.2.2.2.2.1
  have h2hi : lowerRatio p.2 < (4 / 13 : ℝ) := hd.2.2.2.2.2
  have hQ1 : (0 : ℝ) < ((lowerCD p.1).2 : ℝ) := by
    linarith [lowerCD_ge_one p.1]
  have hQ2 : (0 : ℝ) < ((lowerCD p.2).2 : ℝ) := by
    linarith [lowerCD_ge_one p.2]
  have hP1 : (0 : ℝ) ≤ ((lowerCD p.1).1 : ℝ) := by positivity
  let σ : ℝ := ((lowerCD (p.1 ++ [2])).2 : ℝ) ^ 2 /
    ((lowerCD p.2).2 : ℝ) ^ 2
  have hσ : (3 : ℝ) < σ := by
    dsimp only [σ]
    rw [lowerCD_snoc]
    dsimp only [Prod.snd]
    push_cast
    have hs1' : ((729 : ℝ) / 1024) * ((lowerCD p.2).2 : ℝ)^2 <
        ((lowerCD p.1).2 : ℝ)^2 := by
      dsimp only [lowerScale] at hs1
      rw [lt_div_iff₀ (sq_pos_of_pos hQ2)] at hs1
      exact hs1
    rw [lt_div_iff₀ (sq_pos_of_pos hQ2)]
    have hPlo : ((lowerCD p.1).2 : ℝ) / 4 < ((lowerCD p.1).1 : ℝ) := by
      dsimp only [lowerRatio] at h1lo
      rw [lt_div_iff₀ hQ1] at h1lo
      nlinarith
    have hgrow : (81 / 16 : ℝ) * ((lowerCD p.1).2 : ℝ)^2 <
        (((lowerCD p.1).1 : ℝ) + 2*((lowerCD p.1).2 : ℝ))^2 := by
      have hp : 0 < (((lowerCD p.1).1 : ℝ) - (lowerCD p.1).2 / 4) *
          (((lowerCD p.1).1 : ℝ) + 17 * (lowerCD p.1).2 / 4) := by positivity
      nlinarith
    nlinarith
  have hshift : (1 / 4 : ℝ) < lowerRatio (p.1 ++ [2]) := by
    have hPbound : 25 * ((lowerCD p.1).1 : ℝ) < 9 * ((lowerCD p.1).2 : ℝ) := by
      dsimp only [lowerRatio] at h1hi
      rw [div_lt_iff₀ hQ1] at h1hi
      nlinarith
    dsimp only [lowerRatio]
    rw [lowerCD_snoc]
    dsimp only [Prod.fst, Prod.snd]
    push_cast
    rw [lt_div_iff₀ (by nlinarith : 0 < ((lowerCD p.1).1 : ℝ) + 2*((lowerCD p.1).2 : ℝ))]
    nlinarith
  have hscale : σ = ((lowerCD (p.1 ++ [2])).2 : ℝ) ^ 2 /
      ((lowerCD p.2).2 : ℝ) ^ 2 := rfl
  constructor
  · simpa using
      (width_lt_append_append_three (σ := σ) (u₁ := p.1 ++ [2]) (u₂ := p.2)
        (d₁ := (1 : ℕ+)) (d₂ := (2 : ℕ+)) hσ hshift h2lo h2hi hscale (by
          dsimp only [PiHi, PiLo]
          norm_num))
  constructor
  · simpa using
      (width_lt_append_append_three (σ := σ) (u₁ := p.1 ++ [2]) (u₂ := p.2)
        (d₁ := (2 : ℕ+)) (d₂ := (2 : ℕ+)) hσ hshift h2lo h2hi hscale (by
          dsimp only [PiHi, PiLo]
          norm_num))
  · simpa using
      (width_lt_append_append_three (σ := σ) (u₁ := p.1 ++ [2]) (u₂ := p.2)
        (d₁ := (2 : ℕ+)) (d₂ := (3 : ℕ+)) hσ hshift h2lo h2hi hscale (by
          dsimp only [PiHi, PiLo]
          norm_num))


end VerifiedEntryWidths

namespace VerifiedEntry0
set_option autoImplicit true
set_option maxHeartbeats 5000000

open Freiman

private theorem child_of_normalize (p q : LowerPair) (l : LowerLabel)
    (h : lowerNormalize p = q) :
    lowerChild p l = (q.1 ++ l.1.reverse, q.2 ++ l.2) := by
  rw [lowerChild]
  rw [h]

private theorem not_suffix_three_append_one (w : List ℕ+) :
    ¬ ([3] : List ℕ+).IsSuffix (w ++ [1]) := by
  intro h
  have hg := h.getLast (by simp)
  simpa using hg

private theorem not_suffix_three_append_two (w : List ℕ+) :
    ¬ ([3] : List ℕ+).IsSuffix (w ++ [2]) := by
  intro h
  have hg := h.getLast (by simp)
  simpa using hg

private theorem not_suffix_three_one_append_two (w : List ℕ+) :
    ¬ ([3, 1] : List ℕ+).IsSuffix (w ++ [2]) := by
  intro h
  have hg := h.getLast (by simp)
  simpa using hg

private theorem not_suffix_three_one_append_three (w : List ℕ+) :
    ¬ ([3, 1] : List ℕ+).IsSuffix (w ++ [3]) := by
  intro h
  have hg := h.getLast (by simp)
  simpa using hg

private theorem not_suffix_three_append_three_one (w : List ℕ+) :
    ¬ ([3] : List ℕ+).IsSuffix (w ++ [3, 1]) := by
  intro h
  have hg := h.getLast (by simp)
  simpa using hg

private theorem not_suffix_three_append_three_two (w : List ℕ+) :
    ¬ ([3] : List ℕ+).IsSuffix (w ++ [3, 2]) := by
  intro h
  have hg := h.getLast (by simp)
  simpa using hg

private theorem not_suffix_three_one_append_three_two (w : List ℕ+) :
    ¬ ([3, 1] : List ℕ+).IsSuffix (w ++ [3, 2]) := by
  intro h
  have hg := h.getLast (by simp)
  simpa using hg
private theorem label_good
    (hstrict : ∀ q : LowerPair, lowerEndpoint q false < lowerEndpoint q true)
    (p : LowerPair) (hc : lowerEntryContext .threeEven p) (hd : lowerEntryDomain p)
    (ho : lowerEntryChildOrientation p) (hv : lowerEntryVirtualNN p)
    (hr : lowerEntryRowsHold p (lowerEntryGoodRows .threeEven)) :
    lowerStrictGood (lowerChild p ([1], [])) := by
  simp only [lowerEntryContext] at hc
  rcases hc with ⟨hn, hpar, hend₂, hend₁, hclass⟩
  rcases p with ⟨u, v⟩
  change [3].IsSuffix u at hend₁
  change [3].IsSuffix v at hend₂
  rcases hend₁ with ⟨u', hu⟩
  rcases hend₂ with ⟨v', hv'⟩
  subst u
  subst v
  simp only [Prod.fst, Prod.snd, List.length_append, List.length_cons,
    List.length_nil] at hpar hclass
  have huodd : u'.length % 2 = 1 := by omega
  have hvodd : v'.length % 2 = 1 := by omega
  simp [lowerEntryChildOrientation, lowerEntryLabels, lowerChild, hn] at ho
  rcases ho with ⟨ho1, ho21, ho31, ho22, ho23, ho32⟩
  have hn1 : lowerNormalize (u' ++ [3, 1], v' ++ [3]) = (v' ++ [3], u' ++ [3, 1]) := by
    simp [lowerNormalize, not_le_of_gt ho1]
  simp [lowerEntryRowsHold, lowerEntryGoodRows, lowerEntryActualDifference] at hr
  rcases hr with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26⟩
  rw [child_of_normalize _ _ _ hn]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.append_assoc,
    List.cons_append]
  simp only [lowerStrictGood, max_lt_iff, lt_min_iff]
  refine ⟨⟨hstrict _, ?_⟩, ?_, hstrict _⟩
  · rw [child_of_normalize _ _ _ hn1, child_of_normalize _ _ _ hn1]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.append_assoc,
      List.cons_append]
    by_cases ha : lowerWidth (u' ++ [3, 1]) ≤ lowerWidth (v' ++ [3, 1]) <;>
    by_cases hb : lowerWidth (u' ++ [3, 1]) ≤ lowerWidth (v' ++ [3, 2]) <;>
      simp [lowerEndpoint, lowerEndpointWords, lowerEqualWords, lowerNaturalWords,
        lowerNaturalShort, lowerEndpointSuffix, lowerNormalize, lowerEnds,
        huodd, hvodd, ha, hb, not_suffix_three_append_one,
        not_suffix_three_append_two, not_suffix_three_one_append_two,
        not_suffix_three_one_append_three, not_suffix_three_append_three_one,
        not_suffix_three_append_three_two,
        not_suffix_three_one_append_three_two] <;>
      split_ifs <;>
      (try simp only [List.append_assoc, List.cons_append, List.nil_append]) <;>
      linarith
  · rw [child_of_normalize _ _ _ hn1, child_of_normalize _ _ _ hn1]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.append_assoc,
      List.cons_append]
    by_cases ha : lowerWidth (u' ++ [3, 1]) ≤ lowerWidth (v' ++ [3, 1]) <;>
    by_cases hb : lowerWidth (u' ++ [3, 1]) ≤ lowerWidth (v' ++ [3, 2]) <;>
      simp [lowerEndpoint, lowerEndpointWords, lowerEqualWords, lowerNaturalWords,
        lowerNaturalShort, lowerEndpointSuffix, lowerNormalize, lowerEnds,
        huodd, hvodd, ha, hb, not_suffix_three_append_one,
        not_suffix_three_append_two, not_suffix_three_one_append_two,
        not_suffix_three_one_append_three, not_suffix_three_append_three_one,
        not_suffix_three_append_three_two,
        not_suffix_three_one_append_three_two] <;>
      split_ifs <;>
      (try simp only [List.append_assoc, List.cons_append, List.nil_append]) <;>
      linarith

end VerifiedEntry0

namespace VerifiedEntry1
set_option autoImplicit true
set_option maxHeartbeats 5000000

open Freiman

private theorem child_of_normalize (p q : LowerPair) (l : LowerLabel)
    (h : lowerNormalize p = q) :
    lowerChild p l = (q.1 ++ l.1.reverse, q.2 ++ l.2) := by
  rw [lowerChild]
  rw [h]

private theorem equal_words_natural (p : LowerPair) (upper : Bool)
    (hp : p.1.length % 2 = p.2.length % 2)
    (hn : lowerNaturalShort p.1 upper = true ∨
      lowerNaturalShort p.2 upper = true) :
    lowerEqualWords p upper = lowerNaturalWords p upper := by
  rcases p with ⟨u, v⟩
  simp only [Prod.fst, Prod.snd] at hp hn ⊢
  by_cases hw : lowerWidth v ≤ lowerWidth u
  · rcases hn with hn | hn <;>
      simp [lowerEqualWords, lowerNaturalWords, lowerNormalize, hw, hn]
  · rcases hn with hn | hn <;>
      simp [lowerEqualWords, lowerNaturalWords, lowerNormalize, hw, hn]

private theorem equal_even_false_options (x y : List ℕ+)
    (hx : x.length % 2 = 0) (hy : y.length % 2 = 0)
    (hsx : lowerNaturalShort x false = false)
    (hsy : lowerNaturalShort y false = false) :
    lowerEqualWords (x,y) false = (x ++ [3], y ++ [3]) ∨
    lowerEqualWords (x,y) false = (x ++ [3], y ++ [2,1,3]) ∨
    lowerEqualWords (x,y) false = (x ++ [2,1,3], y ++ [3]) := by
  by_cases hw : lowerWidth y ≤ lowerWidth x
  · by_cases hs : lowerWidth (x ++ [3]) ≤ (7/5:ℝ) * lowerWidth (y ++ [3])
    · right; left
      simp [lowerEqualWords, lowerNormalize, hw, hs, hsx, hsy,
        lowerEndpointSuffix, hx, hy]
    · left
      simp [lowerEqualWords, lowerNormalize, hw, hs, hsx, hsy,
        lowerEndpointSuffix, hx, hy]
  · by_cases hs : lowerWidth (y ++ [3]) ≤ (7/5:ℝ) * lowerWidth (x ++ [3])
    · right; right
      simp [lowerEqualWords, lowerNormalize, hw, hs, hsx, hsy,
        lowerEndpointSuffix, hx, hy]
    · left
      simp [lowerEqualWords, lowerNormalize, hw, hs, hsx, hsy,
        lowerEndpointSuffix, hx, hy]

private theorem not_suffix_three_append_one (w : List ℕ+) :
    ¬ ([3] : List ℕ+).IsSuffix (w ++ [1]) := by
  intro h
  have hg := h.getLast (by simp)
  simpa using hg

private theorem not_suffix_three_append_two (w : List ℕ+) :
    ¬ ([3] : List ℕ+).IsSuffix (w ++ [2]) := by
  intro h
  have hg := h.getLast (by simp)
  simpa using hg

private theorem not_suffix_three_one_append_two (w : List ℕ+) :
    ¬ ([3, 1] : List ℕ+).IsSuffix (w ++ [2]) := by
  intro h
  have hg := h.getLast (by simp)
  simpa using hg

private theorem not_suffix_three_one_append_three (w : List ℕ+) :
    ¬ ([3, 1] : List ℕ+).IsSuffix (w ++ [3]) := by
  intro h
  have hg := h.getLast (by simp)
  simpa using hg

private theorem not_suffix_three_append_three_one (w : List ℕ+) :
    ¬ ([3] : List ℕ+).IsSuffix (w ++ [3, 1]) := by
  intro h
  have hg := h.getLast (by simp)
  simpa using hg

private theorem not_suffix_three_append_three_two (w : List ℕ+) :
    ¬ ([3] : List ℕ+).IsSuffix (w ++ [3, 2]) := by
  intro h
  have hg := h.getLast (by simp)
  simpa using hg

private theorem not_suffix_three_one_append_three_two (w : List ℕ+) :
    ¬ ([3, 1] : List ℕ+).IsSuffix (w ++ [3, 2]) := by
  intro h
  have hg := h.getLast (by simp)
  simpa using hg
private theorem label_good
    (hstrict : ∀ q : LowerPair, lowerEndpoint q false < lowerEndpoint q true)
    (p : LowerPair) (hc : lowerEntryContext .threeEven p) (hd : lowerEntryDomain p)
    (ho : lowerEntryChildOrientation p) (hv : lowerEntryVirtualNN p)
    (hr : lowerEntryRowsHold p (lowerEntryGoodRows .threeEven)) :
    lowerStrictGood (lowerChild p ([2], [1])) := by
  simp only [lowerEntryContext] at hc
  rcases hc with ⟨hn, hpar, hend₂, hend₁, hclass⟩
  rcases p with ⟨u, v⟩
  change [3].IsSuffix u at hend₁
  change [3].IsSuffix v at hend₂
  rcases hend₁ with ⟨u', hu⟩
  rcases hend₂ with ⟨v', hv'⟩
  subst u
  subst v
  simp only [Prod.fst, Prod.snd, List.length_append, List.length_cons,
    List.length_nil] at hpar hclass
  have huodd : u'.length % 2 = 1 := by omega
  have hvodd : v'.length % 2 = 1 := by omega
  have hu32odd : (u' ++ [3, 2]).length % 2 = 1 := by simp; omega
  have hv311even : (v' ++ [3, 1, 1]).length % 2 = 0 := by simp; omega
  have hv312even : (v' ++ [3, 1, 2]).length % 2 = 0 := by simp; omega
  have hvadd3 : (v'.length + 3) % 2 = 0 := by omega
  have huadd2 : (u'.length + 2) % 2 = 1 := by omega
  have hvadd4 : (v'.length + 4) % 2 = 1 := by omega
  have huadd3 : (u'.length + 3) % 2 = 0 := by omega
  have hvt := VerifiedEntryTransfers.entry_width_transfers (u' ++ [3], v' ++ [3]) hv
  rcases hvt with ⟨hva1', hva2', hvb1', hvb2', _, _, _, _⟩
  have hva1 : lowerWidth (v' ++ [3,1,1,1]) < lowerWidth (u' ++ [3,2]) := by
    simpa only [Prod.fst, Prod.snd, List.append_assoc, List.cons_append, List.nil_append] using hva1'
  have hva2 : (7/5:ℝ) * lowerWidth (v' ++ [3,1,1,1,3]) < lowerWidth (u' ++ [3,2,3]) := by
    simpa only [Prod.fst, Prod.snd, List.append_assoc, List.cons_append, List.nil_append] using hva2'
  have hvb1 : lowerWidth (v' ++ [3,1,2,1]) < lowerWidth (u' ++ [3,2]) := by
    simpa only [Prod.fst, Prod.snd, List.append_assoc, List.cons_append, List.nil_append] using hvb1'
  have hvb2 : (7/5:ℝ) * lowerWidth (v' ++ [3,1,2,1,3]) < lowerWidth (u' ++ [3,2,3]) := by
    simpa only [Prod.fst, Prod.snd, List.append_assoc, List.cons_append, List.nil_append] using hvb2'
  have hnorm1 : lowerNormalize (v' ++ [3,1,1,1], u' ++ [3,2]) =
      (u' ++ [3,2], v' ++ [3,1,1,1]) := by
    simp [lowerNormalize, not_le_of_gt hva1]
  have hnorm2 : lowerNormalize (v' ++ [3,1,2,1], u' ++ [3,2]) =
      (u' ++ [3,2], v' ++ [3,1,2,1]) := by
    simp [lowerNormalize, not_le_of_gt hvb1]
  have hsu : lowerNaturalShort (u' ++ [3,2]) true = false := by
    simp [lowerNaturalShort, lowerEnds, huodd, ← List.reverse_prefix]
  have hsv1 : lowerNaturalShort (v' ++ [3,1,1,1]) true = false := by
    simp [lowerNaturalShort, lowerEnds, hvodd, ← List.reverse_prefix]
  have hsv2 : lowerNaturalShort (v' ++ [3,1,2,1]) true = false := by
    simp [lowerNaturalShort, lowerEnds, hvodd, ← List.reverse_prefix]
  have heq1 : lowerEqualWords (v' ++ [3,1,1,1], u' ++ [3,2]) true =
      (v' ++ [3,1,1,1,3], u' ++ [3,2,3]) := by
    simp [lowerEqualWords, hnorm1, hsu, hsv1, lowerEndpointSuffix,
      huodd, hvadd4, not_le_of_gt hva1, not_le_of_gt hva2]
  have heq2 : lowerEqualWords (v' ++ [3,1,2,1], u' ++ [3,2]) true =
      (v' ++ [3,1,2,1,3], u' ++ [3,2,3]) := by
    simp [lowerEqualWords, hnorm2, hsu, hsv2, lowerEndpointSuffix,
      huodd, hvadd4, not_le_of_gt hvb1, not_le_of_gt hvb2]
  have hs11 : lowerNaturalShort (v' ++ [3,1,1]) false = false := by
    simp [lowerNaturalShort, lowerEnds, hvodd, hvadd3, ← List.reverse_prefix]
  have hs12 : lowerNaturalShort (v' ++ [3,1,2]) false = false := by
    simp [lowerNaturalShort, lowerEnds, hvodd, hvadd3, ← List.reverse_prefix]
  have hsu21 : lowerNaturalShort (u' ++ [3,2,1]) false = false := by
    simp [lowerNaturalShort, lowerEnds, huodd, huadd3, ← List.reverse_prefix]
  have heql1 := equal_even_false_options (v' ++ [3,1,1]) (u' ++ [3,2,1])
    hv311even (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    hs11 hsu21
  have heql2 := equal_even_false_options (v' ++ [3,1,2]) (u' ++ [3,2,1])
    hv312even (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    hs12 hsu21
  simp [lowerEntryChildOrientation, lowerEntryLabels, lowerChild, hn] at ho
  rcases ho with ⟨ho1, ho21, ho31, ho22, ho23, ho32⟩
  have hn1 : lowerNormalize (u' ++ [3, 2], v' ++ [3, 1]) = (v' ++ [3, 1], u' ++ [3, 2]) := by
    simp [lowerNormalize, not_le_of_gt ho21]
  simp [lowerEntryRowsHold, lowerEntryGoodRows, lowerEntryActualDifference] at hr
  rcases hr with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26⟩
  rw [child_of_normalize _ _ _ hn]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.append_assoc,
    List.cons_append]
  simp only [lowerStrictGood, max_lt_iff, lt_min_iff]
  refine ⟨⟨hstrict _, ?_⟩, ?_, hstrict _⟩
  · rw [child_of_normalize _ _ _ hn1, child_of_normalize _ _ _ hn1]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.append_assoc,
      List.cons_append]
    rcases heql2 with heql2 | heql2 | heql2 <;>
    by_cases ha : lowerWidth (u' ++ [3, 2]) ≤ lowerWidth (v' ++ [3, 1, 1]) <;>
      by_cases hb : lowerWidth (u' ++ [3, 2]) ≤ lowerWidth (v' ++ [3, 1, 2]) <;>
      simp only [lowerEndpoint, lowerEndpointWords] <;>
      (try rw [hv312even, hu32odd, hv311even]) <;>
      simp [ha, hb, hvadd3, huadd2, heq1, heq2, heql2,
        lowerNaturalWords, lowerNaturalShort, lowerEndpointSuffix, lowerEnds,
        huodd, hvodd, ← List.reverse_prefix] <;>
      (try split_ifs) <;>
      (try simp [huodd, hvodd, hvadd3, huadd2, ← List.reverse_prefix]) <;>
      linarith
  · rw [child_of_normalize _ _ _ hn1, child_of_normalize _ _ _ hn1]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.append_assoc,
      List.cons_append]
    rcases heql1 with heql1 | heql1 | heql1 <;>
    by_cases ha : lowerWidth (u' ++ [3, 2]) ≤ lowerWidth (v' ++ [3, 1, 1]) <;>
      by_cases hb : lowerWidth (u' ++ [3, 2]) ≤ lowerWidth (v' ++ [3, 1, 2]) <;>
      simp only [lowerEndpoint, lowerEndpointWords] <;>
      (try rw [hv312even, hu32odd, hv311even]) <;>
      simp [ha, hb, hvadd3, huadd2, heq1, heq2, heql1,
        lowerNaturalWords, lowerNaturalShort, lowerEndpointSuffix, lowerEnds,
        huodd, hvodd, ← List.reverse_prefix] <;>
      (try split_ifs) <;>
      (try simp [huodd, hvodd, hvadd3, huadd2, ← List.reverse_prefix]) <;>
      linarith

end VerifiedEntry1

namespace VerifiedEntry2
set_option autoImplicit true
set_option maxHeartbeats 5000000

open Freiman

private theorem child_of_normalize (p q : LowerPair) (l : LowerLabel)
    (h : lowerNormalize p = q) :
    lowerChild p l = (q.1 ++ l.1.reverse, q.2 ++ l.2) := by
  rw [lowerChild]
  rw [h]

private theorem equal_words_natural (p : LowerPair) (upper : Bool)
    (hp : p.1.length % 2 = p.2.length % 2)
    (hn : lowerNaturalShort p.1 upper = true ∨
      lowerNaturalShort p.2 upper = true) :
    lowerEqualWords p upper = lowerNaturalWords p upper := by
  rcases p with ⟨u, v⟩
  simp only [Prod.fst, Prod.snd] at hp hn ⊢
  by_cases hw : lowerWidth v ≤ lowerWidth u
  · rcases hn with hn | hn <;>
      simp [lowerEqualWords, lowerNaturalWords, lowerNormalize, hw, hn]
  · rcases hn with hn | hn <;>
      simp [lowerEqualWords, lowerNaturalWords, lowerNormalize, hw, hn]

private theorem not_suffix_three_append_one (w : List ℕ+) :
    ¬ ([3] : List ℕ+).IsSuffix (w ++ [1]) := by
  intro h
  have hg := h.getLast (by simp)
  simpa using hg

private theorem not_suffix_three_append_two (w : List ℕ+) :
    ¬ ([3] : List ℕ+).IsSuffix (w ++ [2]) := by
  intro h
  have hg := h.getLast (by simp)
  simpa using hg

private theorem not_suffix_three_one_append_two (w : List ℕ+) :
    ¬ ([3, 1] : List ℕ+).IsSuffix (w ++ [2]) := by
  intro h
  have hg := h.getLast (by simp)
  simpa using hg

private theorem not_suffix_three_one_append_three (w : List ℕ+) :
    ¬ ([3, 1] : List ℕ+).IsSuffix (w ++ [3]) := by
  intro h
  have hg := h.getLast (by simp)
  simpa using hg

private theorem not_suffix_three_append_three_one (w : List ℕ+) :
    ¬ ([3] : List ℕ+).IsSuffix (w ++ [3, 1]) := by
  intro h
  have hg := h.getLast (by simp)
  simpa using hg

private theorem not_suffix_three_append_three_two (w : List ℕ+) :
    ¬ ([3] : List ℕ+).IsSuffix (w ++ [3, 2]) := by
  intro h
  have hg := h.getLast (by simp)
  simpa using hg

private theorem not_suffix_three_one_append_three_two (w : List ℕ+) :
    ¬ ([3, 1] : List ℕ+).IsSuffix (w ++ [3, 2]) := by
  intro h
  have hg := h.getLast (by simp)
  simpa using hg
private theorem label_good
    (hstrict : ∀ q : LowerPair, lowerEndpoint q false < lowerEndpoint q true)
    (p : LowerPair) (hc : lowerEntryContext .threeEven p) (hd : lowerEntryDomain p)
    (ho : lowerEntryChildOrientation p) (hv : lowerEntryVirtualNN p)
    (hr : lowerEntryRowsHold p (lowerEntryGoodRows .threeEven)) :
    lowerStrictGood (lowerChild p ([3], [1])) := by
  simp only [lowerEntryContext] at hc
  rcases hc with ⟨hn, hpar, hend₂, hend₁, hclass⟩
  rcases p with ⟨u, v⟩
  change [3].IsSuffix u at hend₁
  change [3].IsSuffix v at hend₂
  rcases hend₁ with ⟨u', hu⟩
  rcases hend₂ with ⟨v', hv'⟩
  subst u
  subst v
  simp only [Prod.fst, Prod.snd, List.length_append, List.length_cons,
    List.length_nil] at hpar hclass
  have huodd : u'.length % 2 = 1 := by omega
  have hvodd : v'.length % 2 = 1 := by omega
  have hu32odd : (u' ++ [3, 3]).length % 2 = 1 := by simp; omega
  have hv311even : (v' ++ [3, 1, 1]).length % 2 = 0 := by simp; omega
  have hv312even : (v' ++ [3, 1, 2]).length % 2 = 0 := by simp; omega
  have hvadd3 : (v'.length + 3) % 2 = 0 := by omega
  have huadd2 : (u'.length + 2) % 2 = 1 := by omega
  have hvadd4 : (v'.length + 4) % 2 = 1 := by omega
  have huadd3 : (u'.length + 3) % 2 = 0 := by omega
  have hvt := VerifiedEntryTransfers.entry_width_transfers (u' ++ [3], v' ++ [3]) hv
  rcases hvt with ⟨_, _, _, _, hva1', hva2', hvb1', hvb2'⟩
  have hva1 : lowerWidth (v' ++ [3,1,1,1]) < lowerWidth (u' ++ [3,3]) := by
    simpa only [Prod.fst, Prod.snd, List.append_assoc, List.cons_append, List.nil_append] using hva1'
  have hva2 : (7/5:ℝ) * lowerWidth (v' ++ [3,1,1,1,3]) < lowerWidth (u' ++ [3,3,3]) := by
    simpa only [Prod.fst, Prod.snd, List.append_assoc, List.cons_append, List.nil_append] using hva2'
  have hvb1 : lowerWidth (v' ++ [3,1,2,1]) < lowerWidth (u' ++ [3,3]) := by
    simpa only [Prod.fst, Prod.snd, List.append_assoc, List.cons_append, List.nil_append] using hvb1'
  have hvb2 : (7/5:ℝ) * lowerWidth (v' ++ [3,1,2,1,3]) < lowerWidth (u' ++ [3,3,3]) := by
    simpa only [Prod.fst, Prod.snd, List.append_assoc, List.cons_append, List.nil_append] using hvb2'
  have hnorm1 : lowerNormalize (v' ++ [3,1,1,1], u' ++ [3,3]) =
      (u' ++ [3,3], v' ++ [3,1,1,1]) := by
    simp [lowerNormalize, not_le_of_gt hva1]
  have hnorm2 : lowerNormalize (v' ++ [3,1,2,1], u' ++ [3,3]) =
      (u' ++ [3,3], v' ++ [3,1,2,1]) := by
    simp [lowerNormalize, not_le_of_gt hvb1]
  have hsu : lowerNaturalShort (u' ++ [3,3]) true = false := by
    simp [lowerNaturalShort, lowerEnds, huodd, ← List.reverse_prefix]
  have hsv1 : lowerNaturalShort (v' ++ [3,1,1,1]) true = false := by
    simp [lowerNaturalShort, lowerEnds, hvodd, ← List.reverse_prefix]
  have hsv2 : lowerNaturalShort (v' ++ [3,1,2,1]) true = false := by
    simp [lowerNaturalShort, lowerEnds, hvodd, ← List.reverse_prefix]
  have heq1 : lowerEqualWords (v' ++ [3,1,1,1], u' ++ [3,3]) true =
      (v' ++ [3,1,1,1,3], u' ++ [3,3,3]) := by
    simp [lowerEqualWords, hnorm1, hsu, hsv1, lowerEndpointSuffix,
      huodd, hvadd4, not_le_of_gt hva1, not_le_of_gt hva2]
  have heq2 : lowerEqualWords (v' ++ [3,1,2,1], u' ++ [3,3]) true =
      (v' ++ [3,1,2,1,3], u' ++ [3,3,3]) := by
    simp [lowerEqualWords, hnorm2, hsu, hsv2, lowerEndpointSuffix,
      huodd, hvadd4, not_le_of_gt hvb1, not_le_of_gt hvb2]
  have heql1 : lowerEqualWords (v' ++ [3,1,1], u' ++ [3,3,1]) false =
      (v' ++ [3,1,1,3], u' ++ [3,3,1,2,1,3]) := by
    rw [equal_words_natural]
    · simp [lowerNaturalWords, lowerNaturalShort, lowerEndpointSuffix, lowerEnds,
        huodd, hvodd, huadd3, hvadd3, ← List.reverse_prefix]
    · simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    · right
      simp [lowerNaturalShort, lowerEnds, huodd, huadd3, ← List.reverse_prefix]
  have heql2 : lowerEqualWords (v' ++ [3,1,2], u' ++ [3,3,1]) false =
      (v' ++ [3,1,2,3], u' ++ [3,3,1,2,1,3]) := by
    rw [equal_words_natural]
    · simp [lowerNaturalWords, lowerNaturalShort, lowerEndpointSuffix, lowerEnds,
        huodd, hvodd, huadd3, hvadd3, ← List.reverse_prefix]
    · simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    · right
      simp [lowerNaturalShort, lowerEnds, huodd, huadd3, ← List.reverse_prefix]
  simp [lowerEntryChildOrientation, lowerEntryLabels, lowerChild, hn] at ho
  rcases ho with ⟨ho1, ho21, ho31, ho22, ho23, ho32⟩
  have hn1 : lowerNormalize (u' ++ [3, 3], v' ++ [3, 1]) = (v' ++ [3, 1], u' ++ [3, 3]) := by
    simp [lowerNormalize, not_le_of_gt ho31]
  simp [lowerEntryRowsHold, lowerEntryGoodRows, lowerEntryActualDifference] at hr
  rcases hr with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26⟩
  rw [child_of_normalize _ _ _ hn]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.append_assoc,
    List.cons_append]
  simp only [lowerStrictGood, max_lt_iff, lt_min_iff]
  refine ⟨⟨hstrict _, ?_⟩, ?_, hstrict _⟩
  · rw [child_of_normalize _ _ _ hn1, child_of_normalize _ _ _ hn1]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.append_assoc,
      List.cons_append]
    by_cases ha : lowerWidth (u' ++ [3, 3]) ≤ lowerWidth (v' ++ [3, 1, 1]) <;>
    by_cases hb : lowerWidth (u' ++ [3, 3]) ≤ lowerWidth (v' ++ [3, 1, 2]) <;>
      simp only [lowerEndpoint, lowerEndpointWords]
    all_goals rw [hv312even, hu32odd, hv311even]
    all_goals simp [ha, hb, hvadd3, huadd2]
    all_goals
      simp [heq1, heq2, heql1, heql2, lowerNaturalWords, lowerNaturalShort,
        lowerEndpointSuffix, lowerEnds, huodd, hvodd,
        hvadd3, huadd2, ← List.reverse_prefix] <;>
      (try split_ifs) <;>
      (try simp [huodd, hvodd, hvadd3, huadd2, ← List.reverse_prefix]) <;>
      linarith
  · rw [child_of_normalize _ _ _ hn1, child_of_normalize _ _ _ hn1]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.append_assoc,
      List.cons_append]
    by_cases ha : lowerWidth (u' ++ [3, 3]) ≤ lowerWidth (v' ++ [3, 1, 1]) <;>
    by_cases hb : lowerWidth (u' ++ [3, 3]) ≤ lowerWidth (v' ++ [3, 1, 2]) <;>
      simp only [lowerEndpoint, lowerEndpointWords]
    all_goals rw [hv312even, hu32odd, hv311even]
    all_goals simp [ha, hb, hvadd3, huadd2]
    all_goals
      simp [heq1, heq2, heql1, heql2, lowerNaturalWords, lowerNaturalShort,
        lowerEndpointSuffix, lowerEnds, huodd, hvodd,
        hvadd3, huadd2, ← List.reverse_prefix] <;>
      (try split_ifs) <;>
      (try simp [huodd, hvodd, hvadd3, huadd2, ← List.reverse_prefix]) <;>
      linarith

end VerifiedEntry2

namespace VerifiedEntry3
set_option autoImplicit true
set_option maxHeartbeats 5000000

open Freiman

private theorem child_of_normalize (p q : LowerPair) (l : LowerLabel)
    (h : lowerNormalize p = q) :
    lowerChild p l = (q.1 ++ l.1.reverse, q.2 ++ l.2) := by
  rw [lowerChild]
  rw [h]

private theorem equal_words_natural (p : LowerPair) (upper : Bool)
    (hp : p.1.length % 2 = p.2.length % 2)
    (hn : lowerNaturalShort p.1 upper = true ∨ lowerNaturalShort p.2 upper = true) :
    lowerEqualWords p upper = lowerNaturalWords p upper := by
  rcases p with ⟨u, v⟩
  simp only [Prod.fst, Prod.snd] at hp hn ⊢
  by_cases hw : lowerWidth v ≤ lowerWidth u
  · rcases hn with hn | hn <;> simp [lowerEqualWords, lowerNaturalWords, lowerNormalize, hw, hn]
  · rcases hn with hn | hn <;> simp [lowerEqualWords, lowerNaturalWords, lowerNormalize, hw, hn]

private theorem mixed_right_wide_upper_natural (a b : List ℕ+)
    (ha : a.length % 2 = 0) (hb : b.length % 2 = 1)
    (hw : lowerWidth a < lowerWidth b) :
    lowerEndpointWords (a,b) true = lowerNaturalWords (a,b) true := by
  simp [lowerEndpointWords, ha, hb, not_le_of_gt hw]

private theorem mixed_right_wide_lower_equal (a b : List ℕ+)
    (ha : a.length % 2 = 0) (hb : b.length % 2 = 1)
    (hw : lowerWidth a < lowerWidth b) :
    lowerEndpointWords (a,b) false = lowerEqualWords (a,b++[1]) false := by
  simp [lowerEndpointWords, ha, hb, not_le_of_gt hw]

private theorem equal_even_false_options (x y : List ℕ+)
    (hx : x.length % 2 = 0) (hy : y.length % 2 = 0)
    (hsx : lowerNaturalShort x false = false)
    (hsy : lowerNaturalShort y false = false) :
    lowerEqualWords (x,y) false = (x ++ [3], y ++ [3]) ∨
    lowerEqualWords (x,y) false = (x ++ [3], y ++ [2,1,3]) ∨
    lowerEqualWords (x,y) false = (x ++ [2,1,3], y ++ [3]) := by
  by_cases hw : lowerWidth y ≤ lowerWidth x
  · by_cases hs : lowerWidth (x ++ [3]) ≤ (7/5:ℝ) * lowerWidth (y ++ [3])
    · right; left
      simp [lowerEqualWords, lowerNormalize, hw, hs, hsx, hsy,
        lowerEndpointSuffix, hx, hy]
    · left
      simp [lowerEqualWords, lowerNormalize, hw, hs, hsx, hsy,
        lowerEndpointSuffix, hx, hy]
  · by_cases hs : lowerWidth (y ++ [3]) ≤ (7/5:ℝ) * lowerWidth (x ++ [3])
    · right; right
      simp [lowerEqualWords, lowerNormalize, hw, hs, hsx, hsy,
        lowerEndpointSuffix, hx, hy]
    · left
      simp [lowerEqualWords, lowerNormalize, hw, hs, hsx, hsy,
        lowerEndpointSuffix, hx, hy]

private theorem not_suffix_three_append_one (w : List ℕ+) :
    ¬ ([3] : List ℕ+).IsSuffix (w ++ [1]) := by
  intro h
  have hg := h.getLast (by simp)
  simpa using hg

private theorem not_suffix_three_append_two (w : List ℕ+) :
    ¬ ([3] : List ℕ+).IsSuffix (w ++ [2]) := by
  intro h
  have hg := h.getLast (by simp)
  simpa using hg

private theorem not_suffix_three_one_append_two (w : List ℕ+) :
    ¬ ([3, 1] : List ℕ+).IsSuffix (w ++ [2]) := by
  intro h
  have hg := h.getLast (by simp)
  simpa using hg

private theorem not_suffix_three_one_append_three (w : List ℕ+) :
    ¬ ([3, 1] : List ℕ+).IsSuffix (w ++ [3]) := by
  intro h
  have hg := h.getLast (by simp)
  simpa using hg

private theorem not_suffix_three_append_three_one (w : List ℕ+) :
    ¬ ([3] : List ℕ+).IsSuffix (w ++ [3, 1]) := by
  intro h
  have hg := h.getLast (by simp)
  simpa using hg

private theorem not_suffix_three_append_three_two (w : List ℕ+) :
    ¬ ([3] : List ℕ+).IsSuffix (w ++ [3, 2]) := by
  intro h
  have hg := h.getLast (by simp)
  simpa using hg

private theorem not_suffix_three_one_append_three_two (w : List ℕ+) :
    ¬ ([3, 1] : List ℕ+).IsSuffix (w ++ [3, 2]) := by
  intro h
  have hg := h.getLast (by simp)
  simpa using hg
private theorem label_good
    (hstrict : ∀ q : LowerPair, lowerEndpoint q false < lowerEndpoint q true)
    (p : LowerPair) (hc : lowerEntryContext .threeEven p) (hd : lowerEntryDomain p)
    (ho : lowerEntryChildOrientation p) (hv : lowerEntryVirtualNN p)
    (hr : lowerEntryRowsHold p (lowerEntryGoodRows .threeEven)) :
    lowerStrictGood (lowerChild p ([2], [2])) := by
  simp only [lowerEntryContext] at hc
  rcases hc with ⟨hn, hpar, hend₂, hend₁, hclass⟩
  rcases p with ⟨u, v⟩
  change [3].IsSuffix u at hend₁
  change [3].IsSuffix v at hend₂
  rcases hend₁ with ⟨u', hu⟩
  rcases hend₂ with ⟨v', hv'⟩
  subst u
  subst v
  simp only [Prod.fst, Prod.snd, List.length_append, List.length_cons,
    List.length_nil] at hpar hclass
  have huodd : u'.length % 2 = 1 := by omega
  have hvodd : v'.length % 2 = 1 := by omega
  have ha1even : (u' ++ [3,2,1]).length % 2 = 0 := by simp; omega
  have ha2even : (u' ++ [3,2,2]).length % 2 = 0 := by simp; omega
  have huadd3 : (u'.length + 3) % 2 = 0 := by omega
  have hvadd2 : (v'.length + 2) % 2 = 1 := by omega
  have hbodd : (v' ++ [3,2]).length % 2 = 1 := by simp; omega
  have hwg := VerifiedEntryWidths.corrected_grandchild_widths (u' ++ [3], v' ++ [3]) hd
  rcases hwg with ⟨hwa1', hwa2', hwa3'⟩
  have hwa1 : lowerWidth (u' ++ [3,2,1]) < lowerWidth (v' ++ [3,2]) := by
    simpa only [Prod.fst, Prod.snd, List.append_assoc, List.cons_append, List.nil_append] using hwa1'
  have hwa2 : lowerWidth (u' ++ [3,2,2]) < lowerWidth (v' ++ [3,2]) := by
    simpa only [Prod.fst, Prod.snd, List.append_assoc, List.cons_append, List.nil_append] using hwa2'
  simp [lowerEntryChildOrientation, lowerEntryLabels, lowerChild, hn] at ho
  rcases ho with ⟨ho1, ho21, ho31, ho22, ho23, ho32⟩
  have hn22 : lowerNormalize (u' ++ [3, 2], v' ++ [3, 2]) = (u' ++ [3, 2], v' ++ [3, 2]) := by
    simp [lowerNormalize, ho22.le]
  simp [lowerEntryRowsHold, lowerEntryGoodRows, lowerEntryActualDifference] at hr
  rcases hr with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26⟩
  have hup1 : lowerEndpoint (u' ++ [3,2,1], v' ++ [3,2]) true =
      4 + prefixEval (u' ++ [3,2,1,1,3]) lowerTau + prefixEval (v' ++ [3,2,3]) lowerTau := by
    simp only [lowerEndpoint, mixed_right_wide_upper_natural _ _ ha1even hbodd hwa1]
    simp [lowerNaturalWords, lowerNaturalShort, lowerEndpointSuffix, lowerEnds,
      huodd, hvodd, huadd3, hvadd2, ← List.reverse_prefix]
  have hup2 : lowerEndpoint (u' ++ [3,2,2], v' ++ [3,2]) true =
      4 + prefixEval (u' ++ [3,2,2,1,3]) lowerTau + prefixEval (v' ++ [3,2,3]) lowerTau := by
    simp only [lowerEndpoint, mixed_right_wide_upper_natural _ _ ha2even hbodd hwa2]
    simp [lowerNaturalWords, lowerNaturalShort, lowerEndpointSuffix, lowerEnds,
      huodd, hvodd, huadd3, hvadd2, ← List.reverse_prefix]
  have hsa1 : lowerNaturalShort (u' ++ [3,2,1]) false = false := by
    simp [lowerNaturalShort, lowerEnds, huodd, huadd3, ← List.reverse_prefix]
  have hsa2 : lowerNaturalShort (u' ++ [3,2,2]) false = false := by
    simp [lowerNaturalShort, lowerEnds, huodd, huadd3, ← List.reverse_prefix]
  have hsb1 : lowerNaturalShort (v' ++ [3,2,1]) false = false := by
    simp [lowerNaturalShort, lowerEnds, hvodd, ← List.reverse_prefix]
  have heql1 := equal_even_false_options (u' ++ [3,2,1]) (v' ++ [3,2,1])
    ha1even (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    hsa1 hsb1
  have heql2 := equal_even_false_options (u' ++ [3,2,2]) (v' ++ [3,2,1])
    ha2even (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    hsa2 hsb1
  rw [child_of_normalize _ _ _ hn]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.append_assoc,
    List.cons_append]
  simp only [lowerStrictGood, max_lt_iff, lt_min_iff]
  refine ⟨⟨hstrict _, ?_⟩, ?_, hstrict _⟩
  · rw [child_of_normalize _ _ _ hn22, child_of_normalize _ _ _ hn22]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.append_assoc,
      List.cons_append]
    rw [hup1]
    simp only [lowerEndpoint, mixed_right_wide_lower_equal _ _ ha2even hbodd hwa2]
    rcases heql2 with heql2 | heql2 | heql2 <;>
      simp [heql2] <;> linarith
  · rw [child_of_normalize _ _ _ hn22, child_of_normalize _ _ _ hn22]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.append_assoc,
      List.cons_append]
    rw [hup2]
    simp only [lowerEndpoint, mixed_right_wide_lower_equal _ _ ha1even hbodd hwa1]
    rcases heql1 with heql1 | heql1 | heql1 <;>
      simp [heql1] <;> linarith

end VerifiedEntry3

namespace VerifiedEntry4
set_option autoImplicit true
set_option maxHeartbeats 5000000

open Freiman

private theorem child_of_normalize (p q : LowerPair) (l : LowerLabel)
    (h : lowerNormalize p = q) :
    lowerChild p l = (q.1 ++ l.1.reverse, q.2 ++ l.2) := by
  rw [lowerChild]
  rw [h]

private theorem equal_words_natural (p : LowerPair) (upper : Bool)
    (hp : p.1.length % 2 = p.2.length % 2)
    (hn : lowerNaturalShort p.1 upper = true ∨ lowerNaturalShort p.2 upper = true) :
    lowerEqualWords p upper = lowerNaturalWords p upper := by
  rcases p with ⟨u, v⟩
  simp only [Prod.fst, Prod.snd] at hp hn ⊢
  by_cases hw : lowerWidth v ≤ lowerWidth u
  · rcases hn with hn | hn <;> simp [lowerEqualWords, lowerNaturalWords, lowerNormalize, hw, hn]
  · rcases hn with hn | hn <;> simp [lowerEqualWords, lowerNaturalWords, lowerNormalize, hw, hn]

private theorem mixed_right_wide_upper_natural (a b : List ℕ+)
    (ha : a.length % 2 = 0) (hb : b.length % 2 = 1)
    (hw : lowerWidth a < lowerWidth b) :
    lowerEndpointWords (a,b) true = lowerNaturalWords (a,b) true := by
  simp [lowerEndpointWords, ha, hb, not_le_of_gt hw]

private theorem mixed_right_wide_lower_equal (a b : List ℕ+)
    (ha : a.length % 2 = 0) (hb : b.length % 2 = 1)
    (hw : lowerWidth a < lowerWidth b) :
    lowerEndpointWords (a,b) false = lowerEqualWords (a,b++[1]) false := by
  simp [lowerEndpointWords, ha, hb, not_le_of_gt hw]

private theorem equal_even_false_options (x y : List ℕ+)
    (hx : x.length % 2 = 0) (hy : y.length % 2 = 0)
    (hsx : lowerNaturalShort x false = false)
    (hsy : lowerNaturalShort y false = false) :
    lowerEqualWords (x,y) false = (x ++ [3], y ++ [3]) ∨
    lowerEqualWords (x,y) false = (x ++ [3], y ++ [2,1,3]) ∨
    lowerEqualWords (x,y) false = (x ++ [2,1,3], y ++ [3]) := by
  by_cases hw : lowerWidth y ≤ lowerWidth x
  · by_cases hs : lowerWidth (x ++ [3]) ≤ (7/5:ℝ) * lowerWidth (y ++ [3])
    · right; left
      simp [lowerEqualWords, lowerNormalize, hw, hs, hsx, hsy,
        lowerEndpointSuffix, hx, hy]
    · left
      simp [lowerEqualWords, lowerNormalize, hw, hs, hsx, hsy,
        lowerEndpointSuffix, hx, hy]
  · by_cases hs : lowerWidth (y ++ [3]) ≤ (7/5:ℝ) * lowerWidth (x ++ [3])
    · right; right
      simp [lowerEqualWords, lowerNormalize, hw, hs, hsx, hsy,
        lowerEndpointSuffix, hx, hy]
    · left
      simp [lowerEqualWords, lowerNormalize, hw, hs, hsx, hsy,
        lowerEndpointSuffix, hx, hy]

private theorem mixed_left_wide_upper_equal (a b : List ℕ+)
    (ha : a.length % 2 = 0) (hb : b.length % 2 = 1)
    (hw : lowerWidth b ≤ lowerWidth a) :
    lowerEndpointWords (a,b) true = lowerEqualWords (a++[1],b) true := by
  simp [lowerEndpointWords, ha, hb, hw]

private theorem mixed_left_wide_lower_natural (a b : List ℕ+)
    (ha : a.length % 2 = 0) (hb : b.length % 2 = 1)
    (hw : lowerWidth b ≤ lowerWidth a) :
    lowerEndpointWords (a,b) false = lowerNaturalWords (a,b) false := by
  simp [lowerEndpointWords, ha, hb, hw]

private theorem equal_odd_true_options (x y : List ℕ+)
    (hx : x.length % 2 = 1) (hy : y.length % 2 = 1)
    (hsx : lowerNaturalShort x true = false)
    (hsy : lowerNaturalShort y true = false) :
    lowerEqualWords (x,y) true = (x ++ [3], y ++ [3]) ∨
    lowerEqualWords (x,y) true = (x ++ [3], y ++ [2,1,3]) ∨
    lowerEqualWords (x,y) true = (x ++ [2,1,3], y ++ [3]) := by
  by_cases hw : lowerWidth y ≤ lowerWidth x
  · by_cases hs : lowerWidth (x ++ [3]) ≤ (7/5:ℝ) * lowerWidth (y ++ [3])
    · right; left
      simp [lowerEqualWords, lowerNormalize, hw, hs, hsx, hsy,
        lowerEndpointSuffix, hx, hy]
    · left
      simp [lowerEqualWords, lowerNormalize, hw, hs, hsx, hsy,
        lowerEndpointSuffix, hx, hy]
  · by_cases hs : lowerWidth (y ++ [3]) ≤ (7/5:ℝ) * lowerWidth (x ++ [3])
    · right; right
      simp [lowerEqualWords, lowerNormalize, hw, hs, hsx, hsy,
        lowerEndpointSuffix, hx, hy]
    · left
      simp [lowerEqualWords, lowerNormalize, hw, hs, hsx, hsy,
        lowerEndpointSuffix, hx, hy]

private theorem not_suffix_three_append_one (w : List ℕ+) :
    ¬ ([3] : List ℕ+).IsSuffix (w ++ [1]) := by
  intro h
  have hg := h.getLast (by simp)
  simpa using hg

private theorem not_suffix_three_append_two (w : List ℕ+) :
    ¬ ([3] : List ℕ+).IsSuffix (w ++ [2]) := by
  intro h
  have hg := h.getLast (by simp)
  simpa using hg

private theorem not_suffix_three_one_append_two (w : List ℕ+) :
    ¬ ([3, 1] : List ℕ+).IsSuffix (w ++ [2]) := by
  intro h
  have hg := h.getLast (by simp)
  simpa using hg

private theorem not_suffix_three_one_append_three (w : List ℕ+) :
    ¬ ([3, 1] : List ℕ+).IsSuffix (w ++ [3]) := by
  intro h
  have hg := h.getLast (by simp)
  simpa using hg

private theorem not_suffix_three_append_three_one (w : List ℕ+) :
    ¬ ([3] : List ℕ+).IsSuffix (w ++ [3, 1]) := by
  intro h
  have hg := h.getLast (by simp)
  simpa using hg

private theorem not_suffix_three_append_three_two (w : List ℕ+) :
    ¬ ([3] : List ℕ+).IsSuffix (w ++ [3, 2]) := by
  intro h
  have hg := h.getLast (by simp)
  simpa using hg

private theorem not_suffix_three_one_append_three_two (w : List ℕ+) :
    ¬ ([3, 1] : List ℕ+).IsSuffix (w ++ [3, 2]) := by
  intro h
  have hg := h.getLast (by simp)
  simpa using hg
private theorem label_good
    (hstrict : ∀ q : LowerPair, lowerEndpoint q false < lowerEndpoint q true)
    (p : LowerPair) (hc : lowerEntryContext .threeEven p) (hd : lowerEntryDomain p)
    (ho : lowerEntryChildOrientation p) (hv : lowerEntryVirtualNN p)
    (hr : lowerEntryRowsHold p (lowerEntryGoodRows .threeEven)) :
    lowerStrictGood (lowerChild p ([2], [3])) := by
  simp only [lowerEntryContext] at hc
  rcases hc with ⟨hn, hpar, hend₂, hend₁, hclass⟩
  rcases p with ⟨u, v⟩
  change [3].IsSuffix u at hend₁
  change [3].IsSuffix v at hend₂
  rcases hend₁ with ⟨u', hu⟩
  rcases hend₂ with ⟨v', hv'⟩
  subst u
  subst v
  simp only [Prod.fst, Prod.snd, List.length_append, List.length_cons,
    List.length_nil] at hpar hclass
  have huodd : u'.length % 2 = 1 := by omega
  have hvodd : v'.length % 2 = 1 := by omega
  have ha1even : (u' ++ [3,2,1]).length % 2 = 0 := by simp; omega
  have ha2even : (u' ++ [3,2,2]).length % 2 = 0 := by simp; omega
  have hbodd : (v' ++ [3,3]).length % 2 = 1 := by simp; omega
  have huadd3 : (u'.length + 3) % 2 = 0 := by omega
  have hvadd2 : (v'.length + 2) % 2 = 1 := by omega
  have hvadd3 : (v'.length + 3) % 2 = 0 := by omega
  have hwg := VerifiedEntryWidths.corrected_grandchild_widths (u' ++ [3], v' ++ [3]) hd
  rcases hwg with ⟨hwa1', hwa2', hwa3'⟩
  have hwa2 : lowerWidth (u' ++ [3,2,2]) < lowerWidth (v' ++ [3,3]) := by
    simpa only [Prod.fst, Prod.snd, List.append_assoc, List.cons_append, List.nil_append] using hwa3'
  simp [lowerEntryChildOrientation, lowerEntryLabels, lowerChild, hn] at ho
  rcases ho with ⟨ho1, ho21, ho31, ho22, ho23, ho32⟩
  have hn23 : lowerNormalize (u' ++ [3, 2], v' ++ [3, 3]) = (u' ++ [3, 2], v' ++ [3, 3]) := by
    simp [lowerNormalize, ho23.le]
  simp [lowerEntryRowsHold, lowerEntryGoodRows, lowerEntryActualDifference] at hr
  rcases hr with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26⟩
  have hup2 : lowerEndpoint (u' ++ [3,2,2], v' ++ [3,3]) true =
      4 + prefixEval (u' ++ [3,2,2,1,3]) lowerTau + prefixEval (v' ++ [3,3,3]) lowerTau := by
    simp only [lowerEndpoint, mixed_right_wide_upper_natural _ _ ha2even hbodd hwa2]
    simp [lowerNaturalWords, lowerNaturalShort, lowerEndpointSuffix, lowerEnds,
      huodd, hvodd, huadd3, hvadd2, hvadd3, ← List.reverse_prefix]
  have hlo2 : lowerEndpoint (u' ++ [3,2,2], v' ++ [3,3]) false =
      4 + prefixEval (u' ++ [3,2,2,3]) lowerTau + prefixEval (v' ++ [3,3,1,2,1,3]) lowerTau := by
    simp only [lowerEndpoint, mixed_right_wide_lower_equal _ _ ha2even hbodd hwa2]
    rw [equal_words_natural]
    · simp [lowerNaturalWords, lowerNaturalShort, lowerEndpointSuffix, lowerEnds,
        huodd, hvodd, huadd3, hvadd2, hvadd3, ← List.reverse_prefix]
    · simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · right
      simp [lowerNaturalShort, lowerEnds, hvodd, hvadd3, ← List.reverse_prefix]
  have hlo1 : lowerEndpoint (u' ++ [3,2,1], v' ++ [3,3]) false =
      4 + prefixEval (u' ++ [3,2,1,3]) lowerTau + prefixEval (v' ++ [3,3,1,2,1,3]) lowerTau := by
    by_cases hw : lowerWidth (v' ++ [3,3]) ≤ lowerWidth (u' ++ [3,2,1])
    · simp only [lowerEndpoint, mixed_left_wide_lower_natural _ _ ha1even hbodd hw]
      simp [lowerNaturalWords, lowerNaturalShort, lowerEndpointSuffix, lowerEnds,
        huodd, hvodd, huadd3, hvadd2, hvadd3, ← List.reverse_prefix]
    · have hwa : lowerWidth (u' ++ [3,2,1]) < lowerWidth (v' ++ [3,3]) := lt_of_not_ge hw
      simp only [lowerEndpoint, mixed_right_wide_lower_equal _ _ ha1even hbodd hwa]
      rw [equal_words_natural]
      · simp [lowerNaturalWords, lowerNaturalShort, lowerEndpointSuffix, lowerEnds,
          huodd, hvodd, huadd3, hvadd2, hvadd3, ← List.reverse_prefix]
      · simp only [List.length_append, List.length_cons, List.length_nil]; omega
      · right
        simp [lowerNaturalShort, lowerEnds, hvodd, hvadd3, ← List.reverse_prefix]
  have hup1 :
      lowerEndpoint (u' ++ [3,2,1], v' ++ [3,3]) true =
        4 + prefixEval (u' ++ [3,2,1,1,3]) lowerTau + prefixEval (v' ++ [3,3,3]) lowerTau ∨
      lowerEndpoint (u' ++ [3,2,1], v' ++ [3,3]) true =
        4 + prefixEval (u' ++ [3,2,1,1,3]) lowerTau + prefixEval (v' ++ [3,3,2,1,3]) lowerTau ∨
      lowerEndpoint (u' ++ [3,2,1], v' ++ [3,3]) true =
        4 + prefixEval (u' ++ [3,2,1,1,2,1,3]) lowerTau + prefixEval (v' ++ [3,3,3]) lowerTau := by
    by_cases hw : lowerWidth (v' ++ [3,3]) ≤ lowerWidth (u' ++ [3,2,1])
    · simp only [lowerEndpoint, mixed_left_wide_upper_equal _ _ ha1even hbodd hw]
      have hxodd : (u' ++ [3,2,1,1]).length % 2 = 1 := by simp; omega
      have hsx : lowerNaturalShort (u' ++ [3,2,1,1]) true = false := by
        simp [lowerNaturalShort, lowerEnds, huodd, ← List.reverse_prefix]
      have hsy : lowerNaturalShort (v' ++ [3,3]) true = false := by
        simp [lowerNaturalShort, lowerEnds, hvodd, hvadd3, ← List.reverse_prefix]
      rcases equal_odd_true_options (u' ++ [3,2,1,1]) (v' ++ [3,3]) hxodd hbodd hsx hsy
        with h | h | h <;> simp [h]
    · have hwa : lowerWidth (u' ++ [3,2,1]) < lowerWidth (v' ++ [3,3]) := lt_of_not_ge hw
      left
      simp only [lowerEndpoint, mixed_right_wide_upper_natural _ _ ha1even hbodd hwa]
      simp [lowerNaturalWords, lowerNaturalShort, lowerEndpointSuffix, lowerEnds,
        huodd, hvodd, huadd3, hvadd2, hvadd3, ← List.reverse_prefix]
  rw [child_of_normalize _ _ _ hn]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.append_assoc,
    List.cons_append]
  simp only [lowerStrictGood, max_lt_iff, lt_min_iff]
  refine ⟨⟨hstrict _, ?_⟩, ?_, hstrict _⟩
  · rw [child_of_normalize _ _ _ hn23, child_of_normalize _ _ _ hn23]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.append_assoc,
      List.cons_append]
    rw [hlo2]
    rcases hup1 with hup1 | hup1 | hup1 <;> rw [hup1] <;> linarith
  · rw [child_of_normalize _ _ _ hn23, child_of_normalize _ _ _ hn23]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.append_assoc,
      List.cons_append]
    rw [hlo1, hup2]
    linarith

end VerifiedEntry4

namespace VerifiedEntry5
set_option autoImplicit true
set_option maxHeartbeats 5000000

open Freiman

private theorem e32_cd_eq (w : List ℕ+) :
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

private theorem e32_q_pos (w : List ℕ+) : 0 < ((lowerCD w).2 : ℝ) := by
  rw [e32_cd_eq]
  exact_mod_cast continuant_denominator_pos w

private theorem e32_tails :
    lowerAlpha ∈ Set.Icc (0 : ℝ) 1 ∧
    lowerBeta ∈ Set.Icc (0 : ℝ) 1 ∧ lowerAlpha < lowerBeta := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 21)
  have hn := Real.sqrt_nonneg (21 : ℝ)
  have hlo : 3 < Real.sqrt (21 : ℝ) := by nlinarith
  have hhi : Real.sqrt (21 : ℝ) < 5 := by nlinarith
  dsimp [lowerAlpha, lowerBeta, Set.mem_Icc]
  constructor
  · constructor <;> linarith
  constructor
  · constructor <;> linarith
  · linarith

private theorem e32_width_formula (w : List ℕ+) :
    lowerWidth w = (lowerBeta - lowerAlpha) /
      ((((lowerCD w).1 : ℝ) * lowerAlpha + (lowerCD w).2) *
       (((lowerCD w).1 : ℝ) * lowerBeta + (lowerCD w).2)) := by
  unfold lowerWidth
  rw [prefixEval_difference w lowerBeta lowerAlpha e32_tails.2.1 e32_tails.1]
  rw [abs_of_pos (sub_pos.mpr e32_tails.2.2), e32_cd_eq]
  ring

private theorem e32_width_pos (w : List ℕ+) : 0 < lowerWidth w := by
  rw [e32_width_formula]
  have hq := e32_q_pos w
  have ha : 0 ≤ lowerAlpha := e32_tails.1.1
  have hb : 0 ≤ lowerBeta := e32_tails.2.1.1
  exact div_pos (sub_pos.mpr e32_tails.2.2) (mul_pos (by positivity) (by positivity))

private theorem e32_width_lt_of_cd (u v : List ℕ+)
    (hc : ((lowerCD u).1 : ℝ) ≤ ((lowerCD v).1 : ℝ))
    (hd : ((lowerCD u).2 : ℝ) < ((lowerCD v).2 : ℝ)) :
    lowerWidth v < lowerWidth u := by
  rw [e32_width_formula v, e32_width_formula u]
  have ha : 0 ≤ lowerAlpha := e32_tails.1.1
  have hb : 0 ≤ lowerBeta := e32_tails.2.1.1
  have hdu := e32_q_pos u
  have hdv := e32_q_pos v
  have hA : ((lowerCD u).1 : ℝ) * lowerAlpha + (lowerCD u).2 <
      ((lowerCD v).1 : ℝ) * lowerAlpha + (lowerCD v).2 := by
    have hmul := mul_nonneg (sub_nonneg.mpr hc) ha
    nlinarith
  have hB : ((lowerCD u).1 : ℝ) * lowerBeta + (lowerCD u).2 <
      ((lowerCD v).1 : ℝ) * lowerBeta + (lowerCD v).2 := by
    have hmul := mul_nonneg (sub_nonneg.mpr hc) hb
    nlinarith
  have hAu : 0 < ((lowerCD u).1 : ℝ) * lowerAlpha + (lowerCD u).2 := by positivity
  have hAv : 0 < ((lowerCD v).1 : ℝ) * lowerAlpha + (lowerCD v).2 := by positivity
  have hBu : 0 < ((lowerCD u).1 : ℝ) * lowerBeta + (lowerCD u).2 := by positivity
  have hBv : 0 < ((lowerCD v).1 : ℝ) * lowerBeta + (lowerCD v).2 := by positivity
  have hden :
      (((lowerCD u).1 : ℝ) * lowerAlpha + (lowerCD u).2) *
        (((lowerCD u).1 : ℝ) * lowerBeta + (lowerCD u).2) <
      (((lowerCD v).1 : ℝ) * lowerAlpha + (lowerCD v).2) *
        (((lowerCD v).1 : ℝ) * lowerBeta + (lowerCD v).2) :=
    mul_lt_mul hA hB.le hBu hAv.le
  rw [div_lt_div_iff₀ (mul_pos hAv hBv) (mul_pos hAu hBu)]
  nlinarith [sub_pos.mpr e32_tails.2.2]


private theorem e32_suffix_widths (w : List ℕ+) (k : ℕ+) (hk : k = 1 ∨ k = 2) :
    lowerWidth (w ++ [2,k,1]) < lowerWidth (w ++ [1,1,1]) ∧
    lowerWidth (w ++ [2,k,1,3]) < lowerWidth (w ++ [1,1,1,3]) := by
  have hd := e32_q_pos w
  have hc : (0:ℝ) ≤ ((lowerCD w).1 : ℝ) := by positivity
  rcases hk with rfl | rfl
  all_goals constructor
  all_goals apply e32_width_lt_of_cd
  all_goals simp [lowerCD, List.foldl_append] at hd hc ⊢
  all_goals push_cast
  all_goals norm_cast at *
  all_goals omega

private theorem e32_transfers (p : LowerPair) (hv : lowerEntryVirtualNN p) :
    lowerWidth (p.2 ++ [2,1,1]) < lowerWidth (p.1 ++ [3]) ∧
    (7/5:ℝ) * lowerWidth (p.2 ++ [2,1,1,3]) < lowerWidth (p.1 ++ [3,3]) ∧
    lowerWidth (p.2 ++ [2,2,1]) < lowerWidth (p.1 ++ [3]) ∧
    (7/5:ℝ) * lowerWidth (p.2 ++ [2,2,1,3]) < lowerWidth (p.1 ++ [3,3]) := by
  rcases hv with ⟨h1,h2⟩
  have h11 := e32_suffix_widths p.2 1 (Or.inl rfl)
  have h21 := e32_suffix_widths p.2 2 (Or.inr rfl)
  have hp := e32_width_pos (p.2 ++ [1,1,1])
  have hp3 := e32_width_pos (p.2 ++ [1,1,1,3])
  refine ⟨?_,?_,?_,?_⟩ <;> nlinarith [h11.1,h11.2,h21.1,h21.2]

private theorem child_of_normalize (p q : LowerPair) (l : LowerLabel)
    (h : lowerNormalize p = q) :
    lowerChild p l = (q.1 ++ l.1.reverse, q.2 ++ l.2) := by
  rw [lowerChild]
  rw [h]

private theorem equal_words_natural (p : LowerPair) (upper : Bool)
    (hp : p.1.length % 2 = p.2.length % 2)
    (hn : lowerNaturalShort p.1 upper = true ∨
      lowerNaturalShort p.2 upper = true) :
    lowerEqualWords p upper = lowerNaturalWords p upper := by
  rcases p with ⟨u, v⟩
  simp only [Prod.fst, Prod.snd] at hp hn ⊢
  by_cases hw : lowerWidth v ≤ lowerWidth u
  · rcases hn with hn | hn <;>
      simp [lowerEqualWords, lowerNaturalWords, lowerNormalize, hw, hn]
  · rcases hn with hn | hn <;>
      simp [lowerEqualWords, lowerNaturalWords, lowerNormalize, hw, hn]

private theorem not_suffix_three_append_one (w : List ℕ+) :
    ¬ ([3] : List ℕ+).IsSuffix (w ++ [1]) := by
  intro h
  have hg := h.getLast (by simp)
  simpa using hg

private theorem not_suffix_three_append_two (w : List ℕ+) :
    ¬ ([3] : List ℕ+).IsSuffix (w ++ [2]) := by
  intro h
  have hg := h.getLast (by simp)
  simpa using hg

private theorem not_suffix_three_one_append_two (w : List ℕ+) :
    ¬ ([3, 1] : List ℕ+).IsSuffix (w ++ [2]) := by
  intro h
  have hg := h.getLast (by simp)
  simpa using hg

private theorem not_suffix_three_one_append_three (w : List ℕ+) :
    ¬ ([3, 1] : List ℕ+).IsSuffix (w ++ [3]) := by
  intro h
  have hg := h.getLast (by simp)
  simpa using hg

private theorem not_suffix_three_append_three_one (w : List ℕ+) :
    ¬ ([3] : List ℕ+).IsSuffix (w ++ [3, 1]) := by
  intro h
  have hg := h.getLast (by simp)
  simpa using hg

private theorem not_suffix_three_append_three_two (w : List ℕ+) :
    ¬ ([3] : List ℕ+).IsSuffix (w ++ [3, 2]) := by
  intro h
  have hg := h.getLast (by simp)
  simpa using hg

private theorem not_suffix_three_one_append_three_two (w : List ℕ+) :
    ¬ ([3, 1] : List ℕ+).IsSuffix (w ++ [3, 2]) := by
  intro h
  have hg := h.getLast (by simp)
  simpa using hg
private theorem label_good
    (hstrict : ∀ q : LowerPair, lowerEndpoint q false < lowerEndpoint q true)
    (p : LowerPair) (hc : lowerEntryContext .threeEven p) (hd : lowerEntryDomain p)
    (ho : lowerEntryChildOrientation p) (hv : lowerEntryVirtualNN p)
    (hr : lowerEntryRowsHold p (lowerEntryGoodRows .threeEven)) :
    lowerStrictGood (lowerChild p ([3], [2])) := by
  simp only [lowerEntryContext] at hc
  rcases hc with ⟨hn, hpar, hend₂, hend₁, hclass⟩
  rcases p with ⟨u, v⟩
  change [3].IsSuffix u at hend₁
  change [3].IsSuffix v at hend₂
  rcases hend₁ with ⟨u', hu⟩
  rcases hend₂ with ⟨v', hv'⟩
  subst u
  subst v
  simp only [Prod.fst, Prod.snd, List.length_append, List.length_cons,
    List.length_nil] at hpar hclass
  have huodd : u'.length % 2 = 1 := by omega
  have hvodd : v'.length % 2 = 1 := by omega
  have hu32odd : (u' ++ [3, 3]).length % 2 = 1 := by simp; omega
  have hv311even : (v' ++ [3, 2, 1]).length % 2 = 0 := by simp; omega
  have hv312even : (v' ++ [3, 2, 2]).length % 2 = 0 := by simp; omega
  have hvadd3 : (v'.length + 3) % 2 = 0 := by omega
  have huadd2 : (u'.length + 2) % 2 = 1 := by omega
  have hvadd4 : (v'.length + 4) % 2 = 1 := by omega
  have huadd3 : (u'.length + 3) % 2 = 0 := by omega
  have hvt := e32_transfers (u' ++ [3], v' ++ [3]) hv
  rcases hvt with ⟨hva1', hva2', hvb1', hvb2'⟩
  have hva1 : lowerWidth (v' ++ [3,2,1,1]) < lowerWidth (u' ++ [3,3]) := by
    simpa only [Prod.fst, Prod.snd, List.append_assoc, List.cons_append, List.nil_append] using hva1'
  have hva2 : (7/5:ℝ) * lowerWidth (v' ++ [3,2,1,1,3]) < lowerWidth (u' ++ [3,3,3]) := by
    simpa only [Prod.fst, Prod.snd, List.append_assoc, List.cons_append, List.nil_append] using hva2'
  have hvb1 : lowerWidth (v' ++ [3,2,2,1]) < lowerWidth (u' ++ [3,3]) := by
    simpa only [Prod.fst, Prod.snd, List.append_assoc, List.cons_append, List.nil_append] using hvb1'
  have hvb2 : (7/5:ℝ) * lowerWidth (v' ++ [3,2,2,1,3]) < lowerWidth (u' ++ [3,3,3]) := by
    simpa only [Prod.fst, Prod.snd, List.append_assoc, List.cons_append, List.nil_append] using hvb2'
  have hnorm1 : lowerNormalize (v' ++ [3,2,1,1], u' ++ [3,3]) =
      (u' ++ [3,3], v' ++ [3,2,1,1]) := by
    simp [lowerNormalize, not_le_of_gt hva1]
  have hnorm2 : lowerNormalize (v' ++ [3,2,2,1], u' ++ [3,3]) =
      (u' ++ [3,3], v' ++ [3,2,2,1]) := by
    simp [lowerNormalize, not_le_of_gt hvb1]
  have hsu : lowerNaturalShort (u' ++ [3,3]) true = false := by
    simp [lowerNaturalShort, lowerEnds, huodd, ← List.reverse_prefix]
  have hsv1 : lowerNaturalShort (v' ++ [3,2,1,1]) true = false := by
    simp [lowerNaturalShort, lowerEnds, hvodd, ← List.reverse_prefix]
  have hsv2 : lowerNaturalShort (v' ++ [3,2,2,1]) true = false := by
    simp [lowerNaturalShort, lowerEnds, hvodd, ← List.reverse_prefix]
  have heq1 : lowerEqualWords (v' ++ [3,2,1,1], u' ++ [3,3]) true =
      (v' ++ [3,2,1,1,3], u' ++ [3,3,3]) := by
    simp [lowerEqualWords, hnorm1, hsu, hsv1, lowerEndpointSuffix,
      huodd, hvadd4, not_le_of_gt hva1, not_le_of_gt hva2]
  have heq2 : lowerEqualWords (v' ++ [3,2,2,1], u' ++ [3,3]) true =
      (v' ++ [3,2,2,1,3], u' ++ [3,3,3]) := by
    simp [lowerEqualWords, hnorm2, hsu, hsv2, lowerEndpointSuffix,
      huodd, hvadd4, not_le_of_gt hvb1, not_le_of_gt hvb2]
  have heql1 : lowerEqualWords (v' ++ [3,2,1], u' ++ [3,3,1]) false =
      (v' ++ [3,2,1,3], u' ++ [3,3,1,2,1,3]) := by
    rw [equal_words_natural]
    · simp [lowerNaturalWords, lowerNaturalShort, lowerEndpointSuffix, lowerEnds,
        huodd, hvodd, huadd3, hvadd3, ← List.reverse_prefix]
    · simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    · right
      simp [lowerNaturalShort, lowerEnds, huodd, huadd3, ← List.reverse_prefix]
  have heql2 : lowerEqualWords (v' ++ [3,2,2], u' ++ [3,3,1]) false =
      (v' ++ [3,2,2,3], u' ++ [3,3,1,2,1,3]) := by
    rw [equal_words_natural]
    · simp [lowerNaturalWords, lowerNaturalShort, lowerEndpointSuffix, lowerEnds,
        huodd, hvodd, huadd3, hvadd3, ← List.reverse_prefix]
    · simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    · right
      simp [lowerNaturalShort, lowerEnds, huodd, huadd3, ← List.reverse_prefix]
  simp [lowerEntryChildOrientation, lowerEntryLabels, lowerChild, hn] at ho
  rcases ho with ⟨ho1, ho21, ho31, ho22, ho23, ho32⟩
  have hn1 : lowerNormalize (u' ++ [3, 3], v' ++ [3, 2]) = (v' ++ [3, 2], u' ++ [3, 3]) := by
    simp [lowerNormalize, not_le_of_gt ho32]
  simp [lowerEntryRowsHold, lowerEntryGoodRows, lowerEntryActualDifference] at hr
  rcases hr with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26⟩
  rw [child_of_normalize _ _ _ hn]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.append_assoc,
    List.cons_append]
  simp only [lowerStrictGood, max_lt_iff, lt_min_iff]
  refine ⟨⟨hstrict _, ?_⟩, ?_, hstrict _⟩
  · rw [child_of_normalize _ _ _ hn1, child_of_normalize _ _ _ hn1]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.append_assoc,
      List.cons_append]
    by_cases ha : lowerWidth (u' ++ [3, 3]) ≤ lowerWidth (v' ++ [3, 2, 1]) <;>
    by_cases hb : lowerWidth (u' ++ [3, 3]) ≤ lowerWidth (v' ++ [3, 2, 2]) <;>
      simp only [lowerEndpoint, lowerEndpointWords]
    all_goals rw [hv312even, hu32odd, hv311even]
    all_goals simp [ha, hb, hvadd3, huadd2]
    all_goals
      simp [heq1, heq2, heql1, heql2, lowerNaturalWords, lowerNaturalShort,
        lowerEndpointSuffix, lowerEnds, huodd, hvodd,
        hvadd3, huadd2, ← List.reverse_prefix] <;>
      (try split_ifs) <;>
      (try simp [huodd, hvodd, hvadd3, huadd2, ← List.reverse_prefix]) <;>
      linarith
  · rw [child_of_normalize _ _ _ hn1, child_of_normalize _ _ _ hn1]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.append_assoc,
      List.cons_append]
    by_cases ha : lowerWidth (u' ++ [3, 3]) ≤ lowerWidth (v' ++ [3, 2, 1]) <;>
    by_cases hb : lowerWidth (u' ++ [3, 3]) ≤ lowerWidth (v' ++ [3, 2, 2]) <;>
      simp only [lowerEndpoint, lowerEndpointWords]
    all_goals rw [hv312even, hu32odd, hv311even]
    all_goals simp [ha, hb, hvadd3, huadd2]
    all_goals
      simp [heq1, heq2, heql1, heql2, lowerNaturalWords, lowerNaturalShort,
        lowerEndpointSuffix, lowerEnds, huodd, hvodd,
        hvadd3, huadd2, ← List.reverse_prefix] <;>
      (try split_ifs) <;>
      (try simp [huodd, hvodd, hvadd3, huadd2, ← List.reverse_prefix]) <;>
      linarith


end VerifiedEntry5

theorem solution (p : LowerPair) (hc : lowerEntryContext .threeEven p) (hd : lowerEntryDomain p)
    (ho : lowerEntryChildOrientation p) (hv : lowerEntryVirtualNN p)
    (hr : lowerEntryRowsHold p (lowerEntryGoodRows .threeEven)) :
    ∀ l ∈ lowerEntryLabels, lowerStrictGood (lowerChild p l) := by
  intro l hl
  simp only [lowerEntryLabels, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl
  · exact VerifiedEntry0.label_good trunk_endpoint_strict_order p hc hd ho hv hr
  · exact VerifiedEntry1.label_good trunk_endpoint_strict_order p hc hd ho hv hr
  · exact VerifiedEntry2.label_good trunk_endpoint_strict_order p hc hd ho hv hr
  · exact VerifiedEntry3.label_good trunk_endpoint_strict_order p hc hd ho hv hr
  · exact VerifiedEntry4.label_good trunk_endpoint_strict_order p hc hd ho hv hr
  · exact VerifiedEntry5.label_good trunk_endpoint_strict_order p hc hd ho hv hr

#print axioms solution
