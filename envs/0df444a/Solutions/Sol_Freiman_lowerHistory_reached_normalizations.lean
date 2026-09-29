-- Prove2me | solution 1 for Freiman.lowerHistory_reached_normalizations
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-13T13:02:15.906272+00:00
-- url     : https://prove2.me/submissions/0dc18da3-8c61-494a-8c96-640da4eab1ab

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic

open Freiman
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Normalizations15

private theorem rawStep_append (base words : LowerPair) (wide : Bool) (l : LowerLabel) :
    lowerHistoryRawStep (lowerHistoryAppend base words) wide l =
      lowerHistoryAppend base (lowerHistoryRawStep words wide l) := by
  cases wide <;> simp [lowerHistoryRawStep, lowerHistoryAppend, List.append_assoc]

private theorem fold_append (base : LowerPair) :
    ∀ (xs : List (LowerLabel × Bool)) (r : LowerPair × Bool),
      List.foldl (fun s step => (lowerHistoryRawStep s.1 s.2 step.1,
        if step.2 then !s.2 else s.2))
          (lowerHistoryAppend base r.1, r.2) xs =
      let z := List.foldl (fun s step => (lowerHistoryRawStep s.1 s.2 step.1,
        if step.2 then !s.2 else s.2)) r xs
      (lowerHistoryAppend base z.1, z.2) := by
  intro xs
  induction xs with
  | nil => intro r; rfl
  | cons step tail ih =>
      intro r
      simp only [List.foldl_cons]
      rw [rawStep_append]
      simpa using ih (lowerHistoryRawStep r.1 r.2 step.1,
        if step.2 then !r.2 else r.2)

private theorem replay_append (base : LowerPair) (p : LowerHistoryPath) (j : ℕ) :
    (lowerHistoryReplay base p j).1 =
      lowerHistoryAppend base (lowerHistoryReplay ([],[]) p j).1 ∧
    (lowerHistoryReplay base p j).2 = (lowerHistoryReplay ([],[]) p j).2 := by
  unfold lowerHistoryReplay
  have hi : lowerHistoryRawStep base false p.entry =
      lowerHistoryAppend base (lowerHistoryRawStep ([],[]) false p.entry) := by
    simpa [lowerHistoryAppend] using rawStep_append base ([],[]) false p.entry
  rw [hi]
  have hf := fold_append base (p.steps.take j)
    (lowerHistoryRawStep ([],[]) false p.entry, p.initialWider)
  exact ⟨by simpa using congrArg Prod.fst hf, by simpa using congrArg Prod.snd hf⟩

private theorem decide_add_odd (m n : ℕ) :
    decide ((m+n) % 2 = 1) =
      (decide (m % 2 = 1)).xor (decide (n % 2 = 1)) := by
  rcases Nat.mod_two_eq_zero_or_one m with hm | hm <;>
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn <;>
    simp [Nat.add_mod, hm, hn]

private theorem even_of_decide_not_odd (n : ℕ) (h : decide (n % 2 = 1) = false) :
    n % 2 = 0 := by
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn
  · exact hn
  · simp [hn] at h

private theorem advance_shape (r : LowerPair × Bool) (s : LowerHistoryState)
    (l : LowerLabel) (reflect : Bool)
    (hshape : s.context.parity =
        (decide (r.1.1.length % 2 = 1), decide (r.1.2.length % 2 = 1)) ∧
      s.wider = r.2) :
    let r' := (lowerHistoryRawStep r.1 r.2 l, if reflect then !r.2 else r.2)
    let s' := lowerHistoryAdvance s l reflect
    s'.context.parity =
        (decide (r'.1.1.length % 2 = 1), decide (r'.1.2.length % 2 = 1)) ∧
      s'.wider = r'.2 := by
  rcases r with ⟨words,wide⟩
  rcases s with ⟨C,swide,marked,previous⟩
  simp only at hshape ⊢
  unfold lowerHistoryAdvance
  dsimp only
  rw [hshape.1, hshape.2]
  cases wide <;> cases reflect <;>
    simp [lowerHistoryAdvance, lowerHistoryRawStep, List.length_append,
      decide_add_odd, Bool.xor_comm]

private theorem fold_shape :
    ∀ (xs : List (LowerLabel × Bool)) (r : LowerPair × Bool) (s : LowerHistoryState),
      (s.context.parity =
          (decide (r.1.1.length % 2 = 1), decide (r.1.2.length % 2 = 1)) ∧
        s.wider = r.2) →
      let rr := List.foldl (fun z step => (lowerHistoryRawStep z.1 z.2 step.1,
        if step.2 then !z.2 else z.2)) r xs
      let ss := xs.foldl (fun z step => lowerHistoryAdvance z step.1 step.2) s
      ss.context.parity =
          (decide (rr.1.1.length % 2 = 1), decide (rr.1.2.length % 2 = 1)) ∧
        ss.wider = rr.2 := by
  intro xs
  induction xs with
  | nil => intro r s hs; exact hs
  | cons step tail ih =>
      intro r s hs
      simp only [List.foldl_cons]
      rcases step with ⟨l,reflect⟩
      apply ih
      exact advance_shape r s l reflect hs

private theorem state_replay_shape (p : LowerHistoryPath) (j : ℕ) :
    let r := lowerHistoryReplay ([],[]) p j
    let s := lowerHistoryStateAt p j
    s.context.parity =
      (decide (r.1.1.length % 2 = 1), decide (r.1.2.length % 2 = 1)) ∧
    s.wider = r.2 := by
  classical
  unfold lowerHistoryReplay lowerHistoryStateAt
  apply fold_shape
  simp [lowerHistoryInitialState, lowerHistoryRawStep]


private theorem normalization_of_width (hwidth : LowerHistoryWidthLaw)
    (base words : LowerPair) (wider strict : Bool)
    (hw : if wider then
      (if strict then lowerWidth (base.1 ++ words.1) < lowerWidth (base.2 ++ words.2)
       else lowerWidth (base.1 ++ words.1) ≤ lowerWidth (base.2 ++ words.2))
    else
      (if strict then lowerWidth (base.2 ++ words.2) < lowerWidth (base.1 ++ words.1)
       else lowerWidth (base.2 ++ words.2) ≤ lowerWidth (base.1 ++ words.1))) :
    lowerHistoryAtBase base [lowerHistoryNormalization words wider strict] := by
  cases wider <;> cases strict
  · exact (hwidth base words).1.mp (by simpa using hw)
  · exact (hwidth base words).2.mp (by simpa using hw)
  · have hn : ¬ lowerWidth (base.2 ++ words.2) < lowerWidth (base.1 ++ words.1) :=
      not_lt_of_ge (by simpa using hw)
    have hc : ¬ lowerHistoryAtBase base [⟨false,true,lowerHistoryWH words⟩] := by
      simpa only [(hwidth base words).2] using hn
    simp only [lowerHistoryAtBase, lowerHistoryConditions, List.mem_singleton,
      lowerHistoryNormalization, certBoundHolds, Bool.false_eq_true,
      Bool.true_eq_false, ↓reduceIte, forall_eq] at hc ⊢
    exact le_of_not_gt hc
  · have hn : ¬ lowerWidth (base.2 ++ words.2) ≤ lowerWidth (base.1 ++ words.1) :=
      not_le_of_gt (by simpa using hw)
    have hc : ¬ lowerHistoryAtBase base [⟨false,false,lowerHistoryWH words⟩] := by
      simpa only [(hwidth base words).1] using hn
    simp only [lowerHistoryAtBase, lowerHistoryConditions, List.mem_singleton,
      lowerHistoryNormalization, certBoundHolds, Bool.false_eq_true,
      Bool.true_eq_false, ↓reduceIte, forall_eq] at hc ⊢
    exact lt_of_not_ge hc

private theorem replay_succ (base : LowerPair) (p : LowerHistoryPath) (i : ℕ)
    (l : LowerLabel) (reflect : Bool) (hget : p.steps[i]? = some (l,reflect)) :
    lowerHistoryReplay base p (i+1) =
      let r := lowerHistoryReplay base p i
      (lowerHistoryRawStep r.1 r.2 l, if reflect then !r.2 else r.2) := by
  unfold lowerHistoryReplay
  rw [List.take_succ, hget]
  simp only [Option.toList_some, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem legal_at : ∀ (steps : List (LowerLabel × Bool))
    (s : LowerHistoryState) (i : ℕ) (l : LowerLabel) (reflect : Bool),
    lowerHistoryLegalSteps s steps → steps[i]? = some (l,reflect) →
    lowerHistoryStepLegal
      ((steps.take i).foldl (fun z step => lowerHistoryAdvance z step.1 step.2) s)
      l reflect := by
  intro steps
  induction steps with
  | nil => intro s i l reflect hs hg; simp at hg
  | cons a tail ih =>
      intro s i l reflect hs hg
      rcases hs with ⟨ha,ht⟩
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hg
          rcases a with ⟨al,ar⟩
          simp only [List.take_zero, List.foldl_nil]
          cases hg
          exact ha
      | succ i =>
          simp only [List.getElem?_cons_succ] at hg
          simp only [List.take_succ_cons, List.foldl_cons]
          exact ih (lowerHistoryAdvance s a.1 a.2) i l reflect ht hg

private theorem weak_width (base : LowerPair) (p : LowerHistoryPath) (j : ℕ)
    (hcompat : lowerHistoryWiderCompatible (lowerHistoryReplay base p j).1
      (lowerHistoryReplay base p j).2) :
    let words := lowerHistoryWordsAt p j
    let wider := (lowerHistoryStateAt p j).wider
    if wider then lowerWidth (base.1 ++ words.1) ≤ lowerWidth (base.2 ++ words.2)
    else lowerWidth (base.2 ++ words.2) ≤ lowerWidth (base.1 ++ words.1) := by
  have happ := Normalizations15.replay_append base p j
  have hshape := Normalizations15.state_replay_shape p j
  change if (lowerHistoryStateAt p j).wider then
    lowerWidth (lowerHistoryAppend base (lowerHistoryReplay ([],[]) p j).1).1 ≤
      lowerWidth (lowerHistoryAppend base (lowerHistoryReplay ([],[]) p j).1).2
    else lowerWidth (lowerHistoryAppend base (lowerHistoryReplay ([],[]) p j).1).2 ≤
      lowerWidth (lowerHistoryAppend base (lowerHistoryReplay ([],[]) p j).1).1
  rw [hshape.2, ← happ.2, ← happ.1]
  simpa [lowerHistoryWiderCompatible] using hcompat

private theorem strict_replay_transfer (base : LowerPair) (p : LowerHistoryPath) (j : ℕ)
    (hw : if (lowerHistoryReplay base p j).2 then
      lowerWidth (lowerHistoryReplay base p j).1.1 <
        lowerWidth (lowerHistoryReplay base p j).1.2
    else lowerWidth (lowerHistoryReplay base p j).1.2 <
        lowerWidth (lowerHistoryReplay base p j).1.1) :
    let words := lowerHistoryWordsAt p j
    let wider := (lowerHistoryStateAt p j).wider
    if wider then lowerWidth (base.1 ++ words.1) < lowerWidth (base.2 ++ words.2)
    else lowerWidth (base.2 ++ words.2) < lowerWidth (base.1 ++ words.1) := by
  have happ := Normalizations15.replay_append base p j
  have hshape := Normalizations15.state_replay_shape p j
  change if (lowerHistoryStateAt p j).wider then
    lowerWidth (lowerHistoryAppend base (lowerHistoryReplay ([],[]) p j).1).1 <
      lowerWidth (lowerHistoryAppend base (lowerHistoryReplay ([],[]) p j).1).2
    else lowerWidth (lowerHistoryAppend base (lowerHistoryReplay ([],[]) p j).1).2 <
      lowerWidth (lowerHistoryAppend base (lowerHistoryReplay ([],[]) p j).1).1
  rw [hshape.2, ← happ.2, ← happ.1]
  exact hw

private theorem strict_width
    (hf : ∀ (p : LowerPair), lowerGood p → lowerParameterBox p →
      let q := lowerNormalize p
      lowerWidth (q.1++[2]) < lowerWidth q.2 ∧
      lowerWidth (q.1++[3]) < lowerWidth q.2 ∧
      lowerWidth (q.1++[1,1]) < lowerWidth q.2 ∧
      lowerWidth (q.2++[1]) < lowerWidth q.1)
    (t : ℝ) (h : ℕ → LowerPair) (n start : ℕ) (base : LowerPair)
    (flip : Bool) (p : LowerHistoryPath)
    (hh : lowerHistory t h n)
    (hreal : lowerHistoryRealizes h start base flip p)
    (hlen : start + p.steps.length = n)
    (hp : lowerHistoryStructural p)
    (i : ℕ) (hi : i < p.steps.length) (l : LowerLabel) (reflect : Bool)
    (hget : p.steps[i]? = some (l,reflect))
    (hl : l ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) :
    let j := i+1
    let words := lowerHistoryWordsAt p j
    let wider := (lowerHistoryStateAt p j).wider
    if wider then lowerWidth (base.1 ++ words.1) < lowerWidth (base.2 ++ words.2)
    else lowerWidth (base.2 ++ words.2) < lowerWidth (base.1 ++ words.1) := by
  have hstate := hh.2.1 (start+i) (by
    omega)
  have hforced := hf (h (start+i)) hstate.2.1 hstate.2.2.2
  have hri := hreal.2.2.2 i hi.le
  let r := lowerHistoryReplay base p i
  let s := lowerHistoryStateAt p i
  have hshape := Normalizations15.state_replay_shape p i
  have happi := Normalizations15.replay_append base p i
  have hswide : s.wider = r.2 := by
    simpa [s, r, happi.2] using hshape.2
  have hlegal : lowerHistoryStepLegal s l reflect := by
    exact legal_at p.steps (lowerHistoryInitialState p) i l reflect hp.2.2.1 hget
  have hnext := replay_succ base p i l reflect hget
  apply strict_replay_transfer base p (i+1)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl
  all_goals
    simp only [lowerHistoryStepLegal] at hlegal
  · have hreflect : reflect = true := hlegal.2.2.2.2.2.2.2.2.1 (by simp) (by simp)
    subst reflect
    cases hrw : r.2
    · have hq : lowerNormalize (h (start+i)) = r.1 := by
        simpa [r, lowerHistoryOrient, hrw] using hri.2.2
      rw [hq] at hforced
      rw [hnext]
      simpa [r, hrw, lowerHistoryRawStep] using hforced.1
    · have hq : lowerNormalize (h (start+i)) = r.1.swap := by
        simpa [r, lowerHistoryOrient, hrw, Prod.swap] using hri.2.2
      rw [hq] at hforced
      rw [hnext]
      simpa [r, hrw, lowerHistoryRawStep, Prod.swap] using hforced.1
  · have hreflect : reflect = true := hlegal.2.2.2.2.2.2.2.2.1 (by simp) (by simp)
    subst reflect
    cases hrw : r.2
    · have hq : lowerNormalize (h (start+i)) = r.1 := by
        simpa [r, lowerHistoryOrient, hrw] using hri.2.2
      rw [hq] at hforced
      rw [hnext]
      simpa [r, hrw, lowerHistoryRawStep] using hforced.2.1
    · have hq : lowerNormalize (h (start+i)) = r.1.swap := by
        simpa [r, lowerHistoryOrient, hrw, Prod.swap] using hri.2.2
      rw [hq] at hforced
      rw [hnext]
      simpa [r, hrw, lowerHistoryRawStep, Prod.swap] using hforced.2.1
  · have hreflect : reflect = false := hlegal.2.2.2.2.2.2.2.1 (by simp)
    subst reflect
    cases hrw : r.2
    · have hq : lowerNormalize (h (start+i)) = r.1 := by
        simpa [r, lowerHistoryOrient, hrw] using hri.2.2
      rw [hq] at hforced
      rw [hnext]
      simpa [r, hrw, lowerHistoryRawStep] using hforced.2.2.2
    · have hq : lowerNormalize (h (start+i)) = r.1.swap := by
        simpa [r, lowerHistoryOrient, hrw, Prod.swap] using hri.2.2
      rw [hq] at hforced
      rw [hnext]
      simpa [r, hrw, lowerHistoryRawStep, Prod.swap] using hforced.2.2.2

end Normalizations15

open Freiman

private theorem normalizations_core
    (hf : ∀ (p : LowerPair), lowerGood p → lowerParameterBox p →
      let q := lowerNormalize p
      lowerWidth (q.1++[2]) < lowerWidth q.2 ∧
      lowerWidth (q.1++[3]) < lowerWidth q.2 ∧
      lowerWidth (q.1++[1,1]) < lowerWidth q.2 ∧
      lowerWidth (q.2++[1]) < lowerWidth q.1)
    (hwidth : LowerHistoryWidthLaw) (t : ℝ) (h : ℕ → LowerPair) (n : ℕ)
    (hh : lowerHistory t h n) (base : LowerPair) (p : LowerHistoryPath)
    (hp : lowerHistoryStructural p) (hr : lowerHistoryReached t h n base p) :
    lowerHistoryNormalizationEvents base p := by
  rcases hr with ⟨start,flip,hlen,hreal,hsource⟩
  intro j hj
  cases j with
  | zero =>
      change lowerHistoryAtBase base
        [lowerHistoryNormalization (lowerHistoryWordsAt p 0)
          (lowerHistoryStateAt p 0).wider false]
      apply Normalizations15.normalization_of_width hwidth
      exact Normalizations15.weak_width base p 0 (hreal.2.2.2 0 (by omega)).2.1
  | succ i =>
      have hi : i < p.steps.length := by omega
      cases hget : p.steps[i]? with
      | none =>
          have hnot :
              ((p.steps[i]?.getD (([],[]),false)).1 ∈
                [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = False := by
            simp [hget]
          change lowerHistoryAtBase base
            [lowerHistoryNormalization (lowerHistoryWordsAt p (i+1))
              (lowerHistoryStateAt p (i+1)).wider
              (decide (((p.steps[i]?.getD (([],[]),false)).1) ∈
                [(([2],[]) : LowerLabel),([3],[]),([],[1])]))]
          rw [show decide
              (((p.steps[i]?.getD (([],[]),false)).1) ∈
                [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false by
            simp [hnot]]
          apply Normalizations15.normalization_of_width hwidth
          exact Normalizations15.weak_width base p (i+1)
            (hreal.2.2.2 (i+1) (by omega)).2.1
      | some step =>
          rcases step with ⟨l,reflect⟩
          by_cases hforced : l ∈
              [(([2],[]) : LowerLabel),([3],[]),([],[1])]
          · change lowerHistoryAtBase base
              [lowerHistoryNormalization (lowerHistoryWordsAt p (i+1))
                (lowerHistoryStateAt p (i+1)).wider
                (decide (((p.steps[i]?.getD (([],[]),false)).1) ∈
                  [(([2],[]) : LowerLabel),([3],[]),([],[1])]))]
            rw [show decide
                (((p.steps[i]?.getD (([],[]),false)).1) ∈
                  [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true by
              simp [hget,hforced]]
            apply Normalizations15.normalization_of_width hwidth
            exact Normalizations15.strict_width hf t h n start base flip p hh hreal hlen hp
              i hi l reflect hget hforced
          · change lowerHistoryAtBase base
              [lowerHistoryNormalization (lowerHistoryWordsAt p (i+1))
                (lowerHistoryStateAt p (i+1)).wider
                (decide (((p.steps[i]?.getD (([],[]),false)).1) ∈
                  [(([2],[]) : LowerLabel),([3],[]),([],[1])]))]
            rw [show decide
                (((p.steps[i]?.getD (([],[]),false)).1) ∈
                  [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false by
              simp [hget,hforced]]
            apply Normalizations15.normalization_of_width hwidth
            exact Normalizations15.weak_width base p (i+1)
              (hreal.2.2.2 (i+1) (by omega)).2.1


theorem solution (hf : ∀ (p : LowerPair), lowerGood p → lowerParameterBox p → let q := lowerNormalize p; lowerWidth (q.1++[2]) < lowerWidth q.2 ∧ lowerWidth (q.1++[3]) < lowerWidth q.2 ∧ lowerWidth (q.1++[1,1]) < lowerWidth q.2 ∧ lowerWidth (q.2++[1]) < lowerWidth q.1) (hwidth : LowerHistoryWidthLaw) (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n)
    (base : LowerPair) (p : LowerHistoryPath) (hp : lowerHistoryStructural p) (hr : lowerHistoryReached t h n base p) :
    lowerHistoryNormalizationEvents base p := by
  exact normalizations_core hf hwidth t h n hh base p hp hr

#print axioms solution
