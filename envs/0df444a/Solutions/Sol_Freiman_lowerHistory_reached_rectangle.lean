-- Prove2me | solution 1 for Freiman.lowerHistory_reached_rectangle
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-13T09:48:11.137894+00:00
-- url     : https://prove2.me/submissions/383e032b-7d00-4938-89a5-0095c3e55e00

import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerHistoryVerification
import Definitions.Def_Freiman_lowerH5Model
import Theorems.Thm_Freiman_lowerEarlyTerminal_ratio_range
import Theorems.Thm_Freiman_lowerEarlyTerminal_ratio_append
import Mathlib.Tactic

open Freiman

private def allowedContexts : List (List ℕ+) :=
  [[1], [2], [3], [3,1], [3,1,3], [3,1,3,1]]

private def storedRectangle (cat : LowerHistoryCatalog) (ctx : List ℕ+) : CertRectangle :=
  if cat = .initial then
    if ctx = [2] then ⟨1/3,9/25,5/19,4/15⟩ else ⟨1/4,1/3,5/19,4/15⟩
  else if ctx = [1] then ⟨1/2,4/5,3/4,4/5⟩
  else if ctx = [2] then ⟨1/3,1/2,3/4,4/5⟩
  else if ctx = [3] then ⟨1/4,1/3,3/4,4/5⟩
  else if ctx = [3,1] then ⟨3/4,4/5,3/4,4/5⟩
  else if ctx = [3,1,3] then ⟨5/19,4/15,3/4,4/5⟩
  else ⟨15/19,19/24,3/4,4/5⟩

private def pathOK (p : LowerHistoryPath) : Bool :=
  !(decide (p.context ∈ allowedContexts)) ||
    decide (p.rectangle = storedRectangle p.catalog p.context)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem cert_L : lowerHistoryPathsL.all pathOK = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem cert_R : lowerHistoryPathsR.all pathOK = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem cert_M : lowerHistoryPathsM.all pathOK = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem cert_X : lowerHistoryPathsX.all pathOK = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem cert_H : lowerHistoryPathsH.all pathOK = true := by
  decide +kernel

private theorem cert_sound {xs : Array LowerHistoryPath}
    (hc : xs.all pathOK = true) (p : LowerHistoryPath)
    (hm : p ∈ xs.toList) (ha : p.context ∈ allowedContexts) :
    p.rectangle = storedRectangle p.catalog p.context := by
  have hma : p ∈ xs := Array.mem_def.mpr hm
  obtain ⟨i, hi, heq⟩ := Array.mem_iff_getElem.mp hma
  have hok := (Array.all_eq_true.mp hc) i hi
  rw [heq] at hok
  have hd : decide (p.context ∈ allowedContexts) = true := decide_eq_true ha
  simp only [pathOK, hd, Bool.not_true, Bool.false_or] at hok
  exact of_decide_eq_true hok

private theorem catalog_rectangle (p : LowerHistoryPath)
    (hm : p ∈ lowerHistoryPaths.toList) (hp : lowerHistoryStructural p) :
    p.rectangle = storedRectangle p.catalog p.context := by
  have ha : p.context ∈ allowedContexts := by
    by_cases hi : p.catalog = .initial
    · have hc := hp.2.1
      simp only [hi, ↓reduceIte] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc.1 with h2 | h3
      · rw [h2]; decide
      · rw [h3]; decide
    · have hc := hp.2.1
      simp only [hi, ↓reduceIte] at hc
      simpa only [allowedContexts, lowerHistoryContextWords] using hc.1
  have hm' : p ∈ lowerHistoryPaths := Array.mem_def.mpr hm
  simp only [lowerHistoryPaths, Array.mem_append] at hm'
  rcases hm' with (((hL | hR) | hM) | hX) | hH
  · exact cert_sound cert_L p (Array.mem_def.mp hL) ha
  · exact cert_sound cert_R p (Array.mem_def.mp hR) ha
  · exact cert_sound cert_M p (Array.mem_def.mp hM) ha
  · exact cert_sound cert_X p (Array.mem_def.mp hX) ha
  · exact cert_sound cert_H p (Array.mem_def.mp hH) ha


private theorem rectangle_prefixEval_snoc (a : ℕ+) : ∀ (ys : List ℕ+) (x : ℝ),
    prefixEval (ys ++ [a]) x = prefixEval ys (1 / ((a : ℝ) + x)) := by
  intro ys
  induction ys with
  | nil =>
      intro x
      rfl
  | cons b ys ih =>
      intro x
      change 1 / ((b : ℝ) + prefixEval (ys ++ [a]) x) =
        1 / ((b : ℝ) + prefixEval ys (1 / ((a : ℝ) + x)))
      rw [ih x]

private theorem boxFold_bounds : ∀ (ctx : List ℕ+) (z : ℚ × ℚ) (x : ℝ),
    0 ≤ (z.1 : ℝ) → (z.1 : ℝ) ≤ x → x ≤ (z.2 : ℝ) →
    let v := ctx.foldl (fun z (a : ℕ) =>
      (1 / ((a : ℚ) + z.2), 1 / ((a : ℚ) + z.1))) z
    (v.1 : ℝ) ≤ prefixEval ctx.reverse x ∧ prefixEval ctx.reverse x ≤ (v.2 : ℝ) := by
  intro ctx
  induction ctx with
  | nil =>
      intro z x hz hlo hhi
      exact ⟨hlo, hhi⟩
  | cons a ctx ih =>
      intro z x hz hlo hhi
      simp only [List.reverse_cons, rectangle_prefixEval_snoc]
      apply ih
      · dsimp only
        push_cast
        have ha : (1 : ℝ) ≤ ((a : ℕ) : ℝ) := by
          exact_mod_cast (Nat.succ_le_of_lt (PNat.pos a))
        exact one_div_nonneg.mpr (by linarith)
      · dsimp only
        push_cast
        apply one_div_le_one_div_of_le
        · have ha : (1 : ℝ) ≤ ((a : ℕ) : ℝ) := by
            exact_mod_cast (Nat.succ_le_of_lt (PNat.pos a))
          linarith
        · linarith
      · dsimp only
        push_cast
        apply one_div_le_one_div_of_le
        · have ha : (1 : ℝ) ≤ ((a : ℕ) : ℝ) := by
            exact_mod_cast (Nat.succ_le_of_lt (PNat.pos a))
          linarith
        · linarith

private theorem ratio_in_context_box (w ctx : List ℕ+)
    (he : lowerEnds w ctx) (hlo : (1 / 4 : ℝ) ≤ lowerRatio w)
    (hhi : lowerRatio w ≤ (4 / 5 : ℝ)) :
    ((lowerH5ContextBox ctx).1 : ℝ) ≤ lowerRatio w ∧
      lowerRatio w ≤ ((lowerH5ContextBox ctx).2 : ℝ) := by
  unfold lowerEnds at he
  rcases he with ⟨u, rfl⟩
  have hrange := lowerEarlyTerminal_ratio_range u
  have hfold := boxFold_bounds ctx ((0, 1) : ℚ × ℚ) (lowerRatio u)
      (by norm_num) (by simpa using hrange.1) (by simpa using hrange.2)
  rw [lowerEarlyTerminal_ratio_append] at hlo hhi ⊢
  simpa only [lowerH5ContextBox, Rat.cast_max, Rat.cast_min,
    Rat.cast_ofNat, Rat.cast_div, Rat.cast_one] using
    And.intro (max_le hlo hfold.1) (le_min hhi hfold.2)

private theorem normalize_box (p : LowerPair) (h : lowerParameterBox p) :
    lowerParameterBox (lowerNormalize p) := by
  unfold lowerNormalize
  split_ifs
  · exact h
  · exact ⟨h.2.2.1,h.2.2.2,h.1,h.2.1⟩

private theorem rectangle_core
    (hfamily : ∀ (f : LowerInitialFamily) (a k v : ℕ),
      lowerEntryDomain (lowerNormalize (lowerFamilyPair f a k v)))
    (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n)
    (base : LowerPair) (p : LowerHistoryPath)
    (hmem : p ∈ lowerHistoryPaths.toList) (hp : lowerHistoryStructural p)
    (hr : lowerHistoryReached t h n base p) :
    certRectangleMem p.rectangle (lowerRatio base.1) (lowerRatio base.2) := by
  rcases hr with ⟨start, flip, hlen, hreal, hsource⟩
  have hb : lowerParameterBox base := by
    by_cases hi : p.catalog = .initial
    · simp only [hi, ↓reduceIte] at hsource
      rcases hsource.2 with ⟨f,a,k,v,hfam,hsel,hbase,hchild⟩
      rw [hbase]
      have hd := hfamily f a k v
      exact ⟨hd.2.2.1.le, hd.2.2.2.1.le.trans (by norm_num),
        hd.2.2.2.2.1.le, hd.2.2.2.2.2.le.trans (by norm_num)⟩
    · simp only [hi, ↓reduceIte] at hsource
      have hs := hh.2.1 (start - 1) (by omega)
      rw [hsource.2.1]
      exact normalize_box _ hs.2.2.2
  have hr1 := ratio_in_context_box base.1 p.context hreal.1.1 hb.1 hb.2.1
  have hrect := catalog_rectangle p hmem hp
  rw [hrect]
  by_cases hi : p.catalog = .initial
  · simp only [if_pos hi] at hsource
    have hd : lowerEntryDomain base := by
      rcases hsource.2 with ⟨f,a,k,v,hfam,hsel,hbase,hchild⟩
      rw [hbase]
      exact hfamily f a k v
    have hs2 : lowerEnds base.2 [3,1,3] := by
      have hh := hreal.2.1
      rw [if_pos hi] at hh
      exact hh
    have hr2 := ratio_in_context_box base.2 [3,1,3] hs2 hb.2.2.1 hb.2.2.2
    have hc := hp.2.1
    simp only [hi, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc.1 with h2 | h3
    · rw [h2] at hr1 ⊢
      norm_num [lowerH5ContextBox] at hr1 hr2
      simpa [storedRectangle, hi, certRectangleMem] using
        And.intro hr1.1 (And.intro hd.2.2.2.1.le (And.intro hr2.1 hr2.2))
    · rw [h3] at hr1 ⊢
      norm_num [lowerH5ContextBox] at hr1 hr2
      simpa [storedRectangle, hi, certRectangleMem] using
        And.intro hr1.1 (And.intro hr1.2 (And.intro hr2.1 hr2.2))
  · simp only [if_neg hi] at hsource
    have hs2 : lowerEnds base.2 [3,1] := by
      have hh := hreal.2.1
      rw [if_neg hi] at hh
      exact hh.1
    have hr2 := ratio_in_context_box base.2 [3,1] hs2 hb.2.2.1 hb.2.2.2
    have hc := hp.2.1
    simp only [hi, ↓reduceIte] at hc
    simp only [lowerHistoryContextWords, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc.1 with h1 | h2 | h3 | h31 | h313 | h3131
    all_goals rw [‹p.context = _›] at hr1 ⊢
    all_goals
      norm_num [lowerH5ContextBox] at hr1 hr2
      simpa [storedRectangle, hi, certRectangleMem] using
        And.intro hr1.1 (And.intro hr1.2 (And.intro hr2.1 hr2.2))


theorem solution (hfamily : ∀ (f : LowerInitialFamily) (a k v : ℕ), lowerEntryDomain (lowerNormalize (lowerFamilyPair f a k v))) (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n)
    (base : LowerPair) (p : LowerHistoryPath) (hmem : p ∈ lowerHistoryPaths.toList) (hp : lowerHistoryStructural p) (hr : lowerHistoryReached t h n base p) :
    certRectangleMem p.rectangle (lowerRatio base.1) (lowerRatio base.2) := by
  exact rectangle_core hfamily t h n hh base p hmem hp hr

#print axioms solution
