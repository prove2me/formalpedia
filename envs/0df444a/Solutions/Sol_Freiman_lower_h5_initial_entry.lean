-- Prove2me | solution 1 for Freiman.lower_h5_initial_entry
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-13T08:27:49.27399+00:00
-- url     : https://prove2.me/submissions/4f02c1d0-2abc-4311-8c74-2de7f2515674

import Definitions.Def_Freiman_lowerH5Verification
import Definitions.Def_Freiman_lowerInitialEntry

set_option autoImplicit false
set_option maxHeartbeats 400000

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


private theorem not_ends_three_one_of_ends_three (w : List ℕ+)
    (h3 : lowerEnds w [3]) : ¬ lowerEnds w [3,1] := by
  rcases h3 with ⟨u, rfl⟩
  simp [lowerEnds, ← List.reverse_prefix]

theorem solution
    (hctx : ∀ (f : LowerInitialFamily) (n k p : ℕ), ∃ c : LowerEntryClass,
      lowerEntryContext c (lowerNormalize (lowerFamilyPair f n k p)) ∧
      lowerFamilyH f n k p = lowerEntryH c (lowerNormalize (lowerFamilyPair f n k p)))
    (hdom : ∀ (f : LowerInitialFamily) (n k p : ℕ),
      lowerEntryDomain (lowerNormalize (lowerFamilyPair f n k p)))
    (f : LowerInitialFamily) (n k p : ℕ) (l : LowerLabel) (hl : l ∈ lowerEntryLabels) :
    ¬(lowerMixed (lowerChild (lowerFamilyPair f n k p) l) ∧
      lowerL (lowerChild (lowerFamilyPair f n k p) l)) := by
  let b := lowerFamilyPair f n k p
  let q := lowerNormalize b
  obtain ⟨c, hc, _⟩ := hctx f n k p
  have hd : lowerEntryDomain q := hdom f n k p
  change lowerEntryContext c q at hc
  have hn : lowerNormalize q = q := hc.1
  have hpar : q.1.length % 2 = q.2.length % 2 := hc.2.1
  have hend : lowerEnds q.2 [3] := hc.2.2.1
  have ho : lowerEntryChildOrientation q := entry_child_orientation_closed q hd hn
  rcases label_cases l hl with rfl | rfl | rfl | rfl | rfl | rfl
  · intro hbad
    have hw : lowerWidth (q.1 ++ [1]) < lowerWidth q.2 := by
      have h := ho (([1] : List ℕ+), ([] : List ℕ+)) (by simp [lowerEntryLabels])
      simpa [lowerEntryChildOrientation, lowerChild, hn] using h
    have hchild : lowerChild b (([1] : List ℕ+), ([] : List ℕ+)) =
        (q.1 ++ [1], q.2) := by
      simp [lowerChild, q]
    have hL := hbad.2
    change lowerL (lowerChild b (([1] : List ℕ+), ([] : List ℕ+))) at hL
    rw [hchild] at hL
    simp only [lowerL, lowerNormalize, not_le_of_gt hw, if_false, Prod.fst] at hL
    apply not_ends_three_one_of_ends_three q.2 hend
    exact hL
  all_goals
    intro hbad
    apply hbad.1
    have hp : (q.1.length + 1) % 2 = (q.2.length + 1) % 2 := by omega
    simpa [lowerChild, q, b] using hp

#print axioms solution
